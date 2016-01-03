signature CODEGEN =
sig
	structure Frame: FRAME
	
    val codegen: Frame.frame ->
				 Tree.stm ->
				 IntBinarySet.set Temp.Table.table ->
				 Frame.frag list ->
				 (Assem.instr list * (IntBinarySet.set Temp.Table.table) * Frame.frag list)
					
end

structure X86Gen: CODEGEN =
struct

structure Frame: FRAME = X86Frame
structure S = Symbol
structure T = Tree
structure Tm = Temp
structure A = Assem
structure F = Frame
structure PT = PrintTree(F)

fun int i =
    if i >= 0 then Int.toString i
    else "-" ^ Int.toString (~i)
	
(* Not very efficient since we do
   real -> string -> real32 -> word -> string conversion *)
fun float r = (Word.toString
		  o MLton.Real32.castToWord
		  o valOf
		  o Real32.fromString
		  o Real.toString) r ^ "h"

fun codegen frame stm regClassMap' frags =
    let
        val ilist = ref (nil: A.instr list)
		val frags' = ref frags

		fun addFrag frag = (frags' := frag :: (!frags'))
		local
			fun isFrag s (Frame.PROC _) = false
			  | isFrag s (Frame.GLOBAL _) = false
			  | isFrag s (Frame.STRING (lab, _)) = S.name lab = s
			  | isFrag s (Frame.NUMBER (lab, _)) = S.name lab = s
			  | isFrag s (Frame.TABLE (lab, _)) = S.name lab = s
		in
			fun hasDataFrag lab = List.exists (isFrag lab) (!frags')
		end
		
        fun result gen =
            let val t = Tm.newtemp ()
            in  gen t; t
            end
			
		(*	Table mapping temps to a set of registers that can end up storing the temp
			Whenever a temp is added as a source or dest for a A.OPER of A.MOVE
			the entry (temp, list of possible registers) is added to the table.
			
			When building the RIG an interference is added to all the precolored nodes
			who are NOT in this list.
		*)
		val regClassMap = ref regClassMap'
		
		fun merge regs write t =
			case Temp.Table.look (!regClassMap, t) of
				NONE => (
					regClassMap := Temp.Table.enter (!regClassMap, t, regs);
					(NONE, t)
				)
			  | SOME regs' =>
				let
					val intersect = IntBinarySet.intersection (regs, regs')
					val (instr, t', regs') =
						if IntBinarySet.isEmpty intersect then
							let
								val t' = Tm.newtemp ()
								val instr = A.MOVE { assem = "\tmovd `d0, `s0"
												   , src = if write then t' else t
												   , dst = if write then t else t'
												   , doc ="x86gen:62,1"}
							in
								(SOME instr, t', regs)
							end
						else (NONE, t, intersect)
				in
					regClassMap := Temp.Table.enter (!regClassMap, t', regs');
					(instr, t')
				end

		fun emit regs (x as A.MOVE {assem, src, dst, doc}) =
			let
				val (instr, dst') = merge regs true dst
				val x' = A.MOVE { assem = assem
								, src = src
								, dst = dst'
								, doc = doc}
			in
				ilist := x' :: (!ilist);
				case instr of
					NONE => ()
				  | SOME instr => (ilist := instr :: (!ilist))
			end
		  | emit regs (x as A.OPER {assem, src, dst, jump, doc}) =
			let
				val (instrs, dst') = ListPair.unzip (List.map (merge regs true) dst)
				val x' = A.OPER { assem = assem
								, src = src
								, dst = dst'
								, jump = jump
								, doc = doc}
			in
				ilist := x' :: (!ilist);
				List.app (fn instr =>
					case instr of
						NONE => ()
					  | SOME instr => (ilist := instr :: (!ilist))
				) instrs
			end
		  | emit regs x = (ilist := x :: (!ilist))
		
		val gp = IntBinarySet.addList (IntBinarySet.empty, [F.EAX, F.EBX, F.ECX, F.EDX, F.ESI, F.EDI])
		val sse = IntBinarySet.addList (IntBinarySet.empty, [F.XMM0, F.XMM1, F.XMM2, F.XMM3, F.XMM4, F.XMM5, F.XMM6, F.XMM7])
		
		val _ = IntBinarySet.app (fn reg =>
			regClassMap := Temp.Table.enter (!regClassMap, reg, IntBinarySet.singleton reg)
		) (IntBinarySet.union (gp, sse))
			
		fun gpArg t =
			let
				val (instr, t') = merge gp false t
			in
				case instr of
					NONE => ()
				  | SOME instr => (ilist := instr :: (!ilist));
				t'
			end
		fun sseArg t =
			let
				val (instr, t') = merge sse false t
			in
				case instr of
					NONE => ()
				  | SOME instr => (ilist := instr :: (!ilist));
				t'
			end
			
		fun forceSize T.DWORD t = t
		  | forceSize T.WORD t = (F.forceSize T.WORD t; t)
		  | forceSize T.BYTE t = (F.forceSize T.BYTE t; t)
		
		fun formatPtr T.BYTE = "byte ptr"
		  | formatPtr T.WORD = "word ptr"
		  | formatPtr T.DWORD = "dword ptr"

        fun moveInstr d s doc =
			case (F.size d, F.size s) of
				(SOME n, SOME m) =>
				if n = m then
					A.MOVE { assem = "\tmov `d0, `s0"
						   , src = gpArg s
						   , dst = d
						   , doc = "x86gen:" ^ doc ^ ".001" }
				else raise Fail "Unexpected n != m"
			  | (SOME n, NONE) =>
				 (* Horrible hack. But have yet to find a test case where it fails *)
				 A.OPER { assem = "\tmov e`d0, `s0"
								  , src = [gpArg s]
								  , dst = [d]
								  , jump = NONE
								  , doc = "x86gen:" ^ doc ^ ".003" }
			  | (NONE, SOME n) =>
				A.MOVE { assem = "\tmovzx `d0, `s0" (* TODO: movsx instead? *)
					   , src = gpArg s
					   , dst = d
					   , doc = "x86gen: " ^ doc ^ ".002"}
			  | (NONE, NONE) =>
				A.MOVE { assem = "\tmov `d0, `s0"
					   , src = gpArg s
					   , dst = d
					   , doc = "x86gen:" ^ doc ^ ".004"}
									   
        fun moveToMem d s size 0 doc = A.OPER {
										 assem = "\tmov " ^ formatPtr size ^ " [`s0], `s1"
                                       , src = [gpArg d, forceSize size (gpArg s)]
                                       , dst = []
                                       , jump = NONE
                                       , doc = "x86gen:" ^ doc}
		  | moveToMem d s size disp doc = A.OPER {
										 assem = "\tmov " ^ formatPtr size ^ " [`s0 + " ^ int disp ^ "], `s1"
                                       , src = [gpArg d, gpArg s]
                                       , dst = []
                                       , jump = NONE
                                       , doc = "x86gen:" ^ doc}
									   
        fun moveConstIntInstr dst c doc = A.OPER { assem = "\tmov `d0, " ^ int c
                                       , src = []
                                       , dst = [dst]
                                       , jump = NONE
                                       , doc = "x86gen:" ^ doc}
									   
		fun moveZeroExtended dst src doc = A.MOVE { assem = "\tmovzx `d0, `s0"
												  , src = gpArg src
												  , dst = dst
												  , doc = "x86gen:" ^ doc}
						
		fun moveConstIntInstr dst c doc =
			A.OPER { assem = "\tmov `d0, " ^ (int c)
				   , src = []
				   , dst = [dst]
				   , jump = NONE
				   , doc = "x86gen:" ^ doc}
		fun moveConstFloatInstr dst c doc =
			let
				val label = "@" ^ float c
			in
				if not (hasDataFrag label) then
					addFrag (Frame.NUMBER (Tm.namedLabel label, float c))
				else ();
				A.OPER { assem = "\tmovss `d0, dword ptr [" ^ label ^ "]"
					   , dst = [dst]
					   , src = []
					   , jump = NONE
					   , doc = "x86gen:" ^ doc}
			end
		
        fun jump lbl doc = A.OPER { assem = "\tjmp " ^ S.name lbl
								  , src = []
								  , dst = []
								  , jump = SOME [lbl]
								  , doc = "x86gen:" ^ doc}

        fun cjump oper lbl ft doc =
            A.OPER { assem = "\t" ^ oper ^ " " ^ S.name lbl
				   , src = []
				   , dst = []
				   , jump = SOME([lbl, ft])
				   , doc = "x86gen:" ^ doc}
				   
        fun compare s1 s2 doc = A.OPER { assem = "\tcmp `s0, `s1"
                                       , src = [gpArg s1, gpArg s2]
                                       , dst = []
                                       , jump = NONE
                                       , doc = "x86gen:" ^ doc}
									   
        fun compareSSE s1 s2 doc = A.OPER { assem = "\tucomiss `s0, `s1"
                                       , src = [sseArg s1, sseArg s2]
                                       , dst = []
                                       , jump = NONE
                                       , doc = "x86gen:" ^ doc}
									   
        fun zero d doc = A.OPER { assem = "\txor `d0, `d0"
                                       , src = []
                                       , dst = [d]
									   , jump = NONE
                                       , doc = "x86gen:" ^ doc}
									   
        fun adjustSP count = A.OPER { assem = "\tadd `d0, " ^ int count
                                    , src = [gpArg F.SP]
                                    , dst = [F.SP]
                                    , jump = NONE
                                    , doc = "x86gen:52"}
			
        fun freeArgs count = adjustSP (4*count)
			
        fun munchStm (T.SEQ (a, b)) = raise (Fail "Unexpected T.SEQ in IR")

          (* MOVE *)
          | munchStm (T.MOVE (T.TEMP t, T.CALL (T.NAME lab, args))) =
            (emit gp (A.OPER { assem = "\tcall " ^ S.name lab
                           , src = List.map gpArg (munchArgs args)
                           , dst = F.calldefs
                           , jump = NONE
                           , doc = "x86gen:1"})
            ; if length args > 0 then
				emit gp (freeArgs (length args))
			  else ()
            ; emit gp (moveInstr t F.EAX "2"))
          | munchStm (T.MOVE (T.TEMP t, T.CALL (e, args))) =
			let
				val func = munchExp e;
			in
            emit gp (A.OPER { assem = "\tcall `s0"
                           , src = List.map gpArg (func :: munchArgs args)
                           , dst = F.calldefs
                           , jump = NONE
                           , doc = "x86gen:1"})
            ; if length args > 0 then
				emit gp (freeArgs (length args))
			  else ()
            ; emit gp (moveInstr t F.EAX "2")
			end
			
          | munchStm (T.MOVE (T.MEM (e1, s), T.CALL (T.NAME lab, args))) =
			let
				val d = munchExp e1;
			in
            emit gp (A.OPER { assem = "\tcall " ^ S.name lab
                           , src = List.map gpArg (munchArgs args)
                           , dst = F.calldefs
                           , jump = NONE
                           , doc = "x86gen:3"})
            ; if length args > 0 then
				emit gp (freeArgs (length args))
			  else ()
            ; emit gp (moveToMem d F.EAX s 0 "4")
			end
          | munchStm (T.MOVE (T.MEM (e1, s), T.CALL (e2, args))) =
			let
				val func = munchExp e2;
				val d = munchExp e1;
			in
            emit gp (A.OPER { assem = "\tcall `s0"
                           , src = List.map gpArg (func :: munchArgs args)
                           , dst = F.calldefs
                           , jump = NONE
                           , doc = "x86gen:3"})
            ; if length args > 0 then
				emit gp (freeArgs (length args))
			  else ()
            ; emit gp (moveToMem d F.EAX s 0 "4")
			end
          | munchStm (T.MOVE (T.MEM (T.INTBINOP (T.PLUS, e, T.CONST (T.INT i)), s), T.NAME lab)) =
			let 
                val dst = munchExp e
            in  
				emit gp (A.OPER { assem = "\tmov " ^ formatPtr s ^ " [`s0 + " ^ int i ^ "], offset " ^ S.name lab
								, src = [gpArg dst]
								, dst = []
								, jump = NONE
								, doc = "x86gen:6,5"})
            end
		  | munchStm (T.MOVE (T.MEM (e, s), T.NAME lab)) =
			let
				val dst = munchExp e
			in
				emit gp (A.OPER { assem = "\tmov " ^ formatPtr s ^ " [`s0], offset " ^ S.name lab
								, src = [gpArg dst]
								, dst = []
								, jump = NONE
								, doc = "x86gen:6,5"})
			end
          | munchStm (T.MOVE (T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT i)), s), e2)) =
			let 
                val dst = munchExp e1
                val src = munchExp e2
            in  
                (emit gp (moveToMem dst src s i "5"))
            end
          | munchStm (T.MOVE (T.MEM (T.INTBINOP (T.PLUS, T.CONST (T.INT i), e1), s), e2)) =
		  	let 
                val dst = munchExp e1
                val src = munchExp e2
            in  
                (emit gp (moveToMem dst src s i "6"))
            end
          | munchStm (T.MOVE (T.MEM (e1, s), e2)) =
            let 
                val dst = munchExp e1
                val src = munchExp e2
            in  
                (emit gp (moveToMem dst src s 0 "7"))
            end
		  | munchStm (T.MOVE (T.TEMP dst, T.INTBINOP(T.PLUS, T.TEMP t, T.CONST (T.INT n)))) =
				emit gp (A.OPER { assem = "\tlea `d0, dword ptr [`s0 + " ^ int n ^"]"
							 , src = [gpArg t]
							 , dst = [gpArg dst]
							 , jump = NONE
							 , doc = "x86gen:7,01"})
          | munchStm (T.MOVE (T.TEMP i, T.CONST (T.DEFINE s))) =
				emit gp (A.OPER { assem = "\tmov `d0, " ^ s
							 , src = []
							 , dst = [gpArg i]
							 , jump = NONE
							 , doc = "x86gen:6,1"})
          | munchStm (T.MOVE (T.TEMP i, T.CONST (T.INT n))) =
				emit gp (moveConstIntInstr i n "7,1")
		  | munchStm (T.MOVE (T.TEMP i, T.CONST (T.FLOAT f))) =
				emit sse (moveConstFloatInstr i f "7,2")
          | munchStm (T.MOVE (T.TEMP i, e2)) =
            let 
                val src = munchExp e2
            in  
                (emit gp (moveInstr i src "8"))
            end
		  | munchStm (T.MOVE (T.NAME dst, x as (T.NAME src))) =
			let
				(* String to global or global to global *)
				val src' = munchExp x
			in
				emit gp (A.OPER { assem = "\tmov " ^ S.name dst ^ ", `s0"
							 , src = [gpArg src']
							 , dst = []
							 , jump = NONE
							 , doc = "x86gen:8,5"})
			end
		   | munchStm (T.MOVE (_, _)) = raise Fail "Unexpected T.MOVE in IR"
		  
          | munchStm (T.LABEL lab) =
			emit gp (A.LABEL { assem = S.name lab ^ ":"
						   , lab = lab
						   , doc = "x86gen:9"})

          (* JUMP *)
          | munchStm (T.INTCJUMP (oper, T.CONST (T.INT i), e2, lab1, lab2)) =
			let
                val e = munchExp e2
                (* Negate the relation of operators with meaningful order *)
                val oper' = case oper of
                    T.REQ => "je"
                  | T.RNEQ => "jne"
                  | T.RLT => "jge"
                  | T.RGT => "jle"
                  | T.RLE => "jg"
                  | T.RGE => "jl"
            in
                emit gp (A.OPER { assem = "\tcmp `s0, " ^ int i
                              , src = [gpArg e]
                              , dst = []
                              , jump = NONE
                              , doc = "x86gen:10"});
                 emit gp (cjump oper' lab1 lab2 "11");
                 emit gp (jump lab2 "12")
            end
          | munchStm (T.INTCJUMP (oper, e1, T.CONST (T.INT i), lab1, lab2)) =
            let
                val e = munchExp e1
				
				val oper' = case oper of
					T.REQ => "je"
				  | T.RNEQ => "jne"
				  | T.RLT => "jl"
				  | T.RGT => "jg"
				  | T.RLE => "jle"
				  | T.RGE => "jge"
            in
                emit gp (A.OPER { assem = "\tcmp `s0, " ^ int i
                              , src = [gpArg e]
                              , dst = []
                              , jump = NONE
                              , doc = "x86gen:13"});
                emit gp (cjump oper' lab1 lab2 "14");
                emit gp (jump lab2 "15")
            end
          | munchStm (T.INTCJUMP (oper, e1, e2, lab1, lab2)) =
            let
                val me1 = munchExp e1
                val me2 = munchExp e2
				
				val oper' = case oper of
					T.REQ => "je"
				  | T.RNEQ => "jne"
				  | T.RLT => "jg"
				  | T.RGT => "jl"
				  | T.RLE => "jge"
				  | T.RGE => "jle"
            in
                (emit gp (compare me2 me1 "16");
                 emit gp (cjump oper' lab1 lab2 "17");
                 emit gp (jump lab2 "18"))
            end
			(* TODO: Write cases for comparing when e1 or e2 is a T.MEM *)
          | munchStm (T.FLOATCJUMP (oper, e1, e2, lab1, lab2)) =
            let
                val me1 = munchExp e1
                val me2 = munchExp e2
				
				val oper' = case oper of
					T.REQ => "je"
				  | T.RNEQ => "jne"
				  | T.RLT => "ja"
				  | T.RGT => "jb"
				  | T.RLE => "jae"
				  | T.RGE => "jbe"
            in
                emit sse (compareSSE me2 me1 "16");
                emit gp (cjump oper' lab1 lab2 "17");
                emit gp (jump lab2 "18")
            end
		  
          | munchStm (T.JUMP (T.NAME lab, llst)) =
				emit gp (jump lab "19")
		  
          | munchStm (T.JUMP (_, _)) = raise (Fail "Invalid JUMP IR") (* Complain no match *)
            

          (* EXP *)
          | munchStm (T.EXP (T.CALL (T.NAME lab, args))) =
				(emit gp (A.OPER { assem = "\tcall " ^ S.name lab
							  , src = List.map gpArg (munchArgs args)
							  , dst = F.calldefs
							  , jump = NONE
							  , doc = "x86gen:20"});
				 if length args > 0 then
					emit gp (freeArgs (length args))
				 else ())
          | munchStm (T.EXP (T.CALL (e, args))) =
			let
				val func = munchExp e
			in
				emit gp (A.OPER { assem = "\tcall `s0"
							  , src = List.map gpArg (func :: munchArgs args)
							  , dst = F.calldefs
							  , jump = NONE
							  , doc = "x86gen:20"});
				 if length args > 0 then
					emit gp (freeArgs (length args))
				 else ()
			end
          | munchStm (T.EXP exp) = (munchExp exp; ())

        and munchArgs args =
			List.map (fn arg =>
				let                          
					val e = munchExp arg
				in
					emit gp (A.OPER { assem = "\tpush `s0"
								  , src = [gpArg e]
								  , dst = []
								  , jump = NONE
								  , doc = "x86gen:21"});
					e
				end) (List.rev args)

        (* Memory access *)
        and munchExp (T.MEM (T.INTBINOP (T.PLUS, e, T.CONST (T.INT n)), s)) =
            result (fn r => emit gp (A.OPER { assem = "\tmov `d0, " ^ formatPtr s ^ " [`s0 + " ^ int n ^ "]"
                                         , src = [gpArg (munchExp e)]
                                         , dst = [r]
                                         , jump = NONE
                                         , doc = "x86gen:22"}))
          | munchExp (T.MEM (T.INTBINOP (T.PLUS, T.CONST (T.INT n), e), s)) =
            result (fn r => emit gp (A.OPER { assem = "\tmov `d0, " ^ formatPtr s ^ " [`s0 + " ^ int n ^ "]"
                                         , src = [gpArg (munchExp e)]
                                         , dst = [r]
                                         , jump = NONE
                                         , doc = "x86gen:23"}))
          | munchExp (T.MEM (T.INTBINOP (T.MINUS, e, T.CONST (T.INT n)), s)) =
            result (fn r => emit gp (A.OPER { assem = "\tmov `d0, " ^ formatPtr s ^ " [`s0 + " ^ int (~n) ^ "]"
                                         , src = [gpArg (munchExp e)]
                                         , dst = [r]
                                         , jump = NONE
                                         , doc = "x86gen:24"}))
          
          | munchExp (T.MEM (e, s)) =
            result (fn r => emit gp (A.OPER { assem = "\tmov `d0, " ^ formatPtr s ^ " [`s0]"
                                         , src = [gpArg (munchExp e)]
                                         , dst = [forceSize s r]
                                         , jump = NONE
                                         , doc = "x86gen:25"}))
          (* PLUS *)
          | munchExp (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT i))) =
            result (fn r =>
				let
                    val e = munchExp e1
                in
					emit gp (moveInstr r e "26");
					emit gp (A.OPER { assem = "\tadd `d0, " ^ int i
                                   , src = [gpArg r]
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:27"})
                end)
          | munchExp (T.INTBINOP (T.PLUS, T.CONST (T.INT i), e1)) =
            result (fn r =>
                let
                    val e = munchExp e1
                in
                    emit gp (moveInstr r e "28");
                     emit gp (A.OPER { assem = "\tadd `d0, " ^ int i
                                   , src = [gpArg r]
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:29"})
                end)
          | munchExp (T.INTBINOP (T.PLUS, e1, e2)) =
            result (fn r =>
                let
                    val e1' = munchExp e1
                    val e2' = munchExp e2
                in
                    emit gp (moveInstr r e1' "30");
                    emit gp (A.OPER { assem = "\tadd `d0, `s1"
                                  , src = List.map gpArg [r, e2']
                                  , dst = [r]
                                  , jump = NONE
                                  , doc = "x86gen:31"})
                end)

          | munchExp (T.FLOATBINOP (T.PLUS,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s),
				T.CONST (T.FLOAT f))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
			in
				emit sse (moveConstFloatInstr r f "31,1");
				emit sse (A.OPER { assem = "\taddss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
							 , src = [sseArg r, gpArg e1']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:31,2"})
			end)
          | munchExp (T.FLOATBINOP (T.PLUS,
				T.CONST (T.FLOAT f),
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s))) =
		  	result (fn r =>
			let
				val e1' = munchExp e1;
			in
				emit sse (moveConstFloatInstr r f "31,3");
				emit sse (A.OPER { assem = "\taddss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
							 , src = [sseArg r, gpArg e1']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:31,4"})
			end)
          | munchExp (T.FLOATBINOP (T.PLUS,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n1)), s1),
				T.MEM (T.INTBINOP (T.PLUS, e2, T.CONST (T.INT n2)), s2))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, " ^ formatPtr s1 ^ " [`s0 + " ^ int n1 ^ "]"
							 , src = gpArg e1'
							 , dst = r
							 , doc = "x86gen:31.5"});
				emit sse (A.OPER { assem = "\taddss `d0, " ^ formatPtr s2 ^ " [`s1 + " ^ int n2 ^ "]"
							 , src = [sseArg r, gpArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:31,5"})
			end)
          | munchExp (T.FLOATBINOP (T.PLUS,
				e1,
				T.MEM (T.INTBINOP (T.PLUS, e2, T.CONST (T.INT n)), s))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e1'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\taddss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
							 , src = [sseArg r, gpArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)
		  | munchExp (T.FLOATBINOP (T.PLUS,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s),
				e2)) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e2'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\taddss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
							 , src = [sseArg r, gpArg e1']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)
		  | munchExp (T.FLOATBINOP (T.PLUS,
				e1,
				e2)) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e2'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\taddss `d0, `s1"
							 , src = [sseArg r, sseArg e1']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)
			
			
            

          (* MINUS *)
          | munchExp (T.INTBINOP (T.MINUS, e1, T.CONST (T.INT i))) =
            result (fn r =>
                let
                    val e = munchExp e1
                in
                    emit gp (moveInstr r e "32");
                    emit gp (A.OPER { assem = "\tsub `d0, " ^ int i
                                         , src = [gpArg r]
                                         , dst = [r]
                                         , jump = NONE
                                         , doc = "x86gen:33"})
                end)
          | munchExp (T.INTBINOP (T.MINUS, T.CONST (T.INT 0), e1)) =
            result (fn r =>
                let
                    val e = munchExp e1
                in
                    emit gp (moveInstr r e "34");
                    emit gp (A.OPER { assem = "\tneg `d0"
                                         , src = [gpArg r]
                                         , dst = [r]
                                         , jump = NONE
                                         , doc = "x86gen:35"})
                end)
          | munchExp (T.INTBINOP (T.MINUS, T.CONST (T.INT i), e1)) =
            result (fn r =>
                let
                   val e = munchExp e1
                in
                    emit gp (moveConstIntInstr r i "36");
                    emit gp (A.OPER { assem = "\tsubl `d0, `s0"
                                  , src = List.map gpArg [e, r]
                                  , dst = [r]
                                  , jump = NONE
                                  , doc = "x86gen:37"})
                end)
          | munchExp (T.INTBINOP (T.MINUS, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
                    emit gp (moveInstr r e1' "38");
                    emit gp (A.OPER { assem = "\tsub `d0, `s1"
                                         , src = List.map gpArg [r, e2']
                                         , dst = [r]
                                         , jump = NONE
                                         , doc = "x86gen:39"})
                end)
		  
          | munchExp (T.FLOATBINOP (T.MINUS,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s),
				T.CONST (T.FLOAT f))) =
			result (fn r =>
				let
					val e1' = munchExp e1;
					val r' = Tm.newtemp ();
				in
					emit sse (A.MOVE { assem = "\tmovss `d0, " ^ formatPtr s ^ " [`s0 + " ^ int n ^ "]"
								 , src = gpArg e1'
								 , dst = r
								 , doc = "x86gen:39,1"});
					emit sse (moveConstFloatInstr r' f "39,2");
					emit sse (A.OPER { assem = "\tsubss `d0, `s1"
								 , src = [sseArg r, gpArg r']
								 , dst = [r]
								 , jump = NONE
								 , doc = "x86gen:39,2"})
				end)
		  | munchExp (T.FLOATBINOP (T.MINUS,
				T.CONST (T.FLOAT f),
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s))) =
			result (fn r =>
				let
					val e1' = munchExp e1;
				in
					emit sse (moveConstFloatInstr r f "39,3");
					emit sse (A.OPER { assem = "\tsubss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
								 , src = [sseArg r, gpArg e1']
								 , dst = [r]
								 , jump = NONE
								 , doc = "x86gen:39,4"})
				end)
          | munchExp (T.FLOATBINOP (T.MINUS,
				T.CONST (T.INT 0),
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s))) =
			(* Negation of floating points is implementing by XOR'ing with
			   2^31, which flips the sign bit. Using SSE this is:
				t = munch e1
				movss t', 0x80000000
				xorps t, t'
			*)
			result (fn r =>
				let
					val e1' = munchExp e1
					val t' = Tm.newtemp ()
					val pow2_31 = "@80000000h"
				in
					if not (hasDataFrag pow2_31) then
						addFrag (Frame.NUMBER (Tm.namedLabel pow2_31, "80000000h"))
					else ();
					emit sse (A.OPER { assem = "\tmovss `d0, dword ptr [" ^ pow2_31 ^ "]"
								 , src = []
								 , dst = [t']
								 , jump = NONE
								 , doc = "x86gen:39,5"});
					emit sse (A.MOVE { assem = "\tmovss `d0, " ^ formatPtr s ^ " [`s0 + " ^ int n ^ "]"
								 , src = gpArg e1'
								 , dst = r
								 , doc = "x86gen:39,6"});
					emit sse (A.OPER { assem = "\txorps `d0, `s1"
								 , src = List.map sseArg [r, t']
								 , dst = [r]
								 , jump = NONE
								 , doc = "x86gen:39,7"})
				end)
          | munchExp (T.FLOATBINOP (T.MINUS,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n1)), s1),
				T.MEM (T.INTBINOP (T.PLUS, e2, T.CONST (T.INT n2)), s2))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, " ^ formatPtr s1 ^ " [`s0 + " ^ int n1 ^ "]"
							 , src = gpArg e1'
							 , dst = r
							 , doc = "x86gen:31,8"});
				emit sse (A.OPER { assem = "\tsubss `d0, " ^ formatPtr s2 ^ " [`s1 + " ^ int n2 ^ "]"
							 , src = [sseArg r, gpArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:31,9"})
			end)
          | munchExp (T.FLOATBINOP (T.MINUS,
				e1,
				T.MEM (T.INTBINOP (T.PLUS, e2, T.CONST (T.INT n)), s))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e1'
							 , dst = r
							 , doc = "x86gen:31,8"});
				emit sse (A.OPER { assem = "\tsubss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
							 , src = [sseArg r, gpArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:31,9"})
			end)
          | munchExp (T.FLOATBINOP (T.MINUS,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s),
				e2)) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, " ^ formatPtr s ^ " [`s0 + " ^ int n ^ "]"
							 , src = gpArg e1'
							 , dst = r
							 , doc = "x86gen:31,8"});
				emit sse (A.OPER { assem = "\tsubss `d0, `s1"
							 , src = [sseArg r, sseArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:31,9"})
			end)
        | munchExp (T.FLOATBINOP (T.MINUS,
				e1,
				e2)) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e2'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\tsubss `d0, `s1"
							 , src = [sseArg r, sseArg e1']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)
            

          (* MULTIPLY *)
          | munchExp (T.INTBINOP (T.MUL, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
                    emit gp (moveInstr r e1' "40");
                    emit gp (A.OPER { assem = "\timul `d0, `s1"
                                         , src = List.map gpArg [r, e2']
                                         , dst = [r]
                                         , jump = NONE
                                         , doc = "x86gen:41"})
                end)
		  
		  | munchExp (T.FLOATBINOP (T.MUL,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n1)), s1),
				T.MEM (T.INTBINOP (T.PLUS, e2, T.CONST (T.INT n2)), s2))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, " ^ formatPtr s1 ^ " [`s0 + " ^ int n1 ^ "]"
							 , src = gpArg e1'
							 , dst = r
							 , doc = "x86gen:41,1"});
				emit sse (A.OPER { assem = "\tmulss `d0, " ^ formatPtr s2 ^ " [`s1 + " ^ int n2 ^ "]"
							 , src = [sseArg r, gpArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,2"})
			end)
		  | munchExp (T.FLOATBINOP (T.MUL,
				e1,
				T.MEM (T.INTBINOP (T.PLUS, e2, T.CONST (T.INT n)), s))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e1'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\tmulss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
							 , src = [sseArg r, gpArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)
		  | munchExp (T.FLOATBINOP (T.MUL,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s),
				e2)) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e2'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\tmulss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
							 , src = [sseArg r, gpArg e1']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)
		  | munchExp (T.FLOATBINOP (T.MUL,
				e1,
				e2)) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e2'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\tmulss `d0, `s1"
							 , src = [sseArg r, sseArg e1']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)
            
			
          (* DIVIDE *)
          | munchExp (T.INTBINOP (T.DIV, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
                    emit gp (moveInstr F.EAX e1' "42");
                    emit gp (A.OPER { assem = "\tcdq"
                                         , src = List.map gpArg [F.EAX, F.EDX]
                                         , dst = [F.EDX]
                                         , jump = NONE
                                         , doc = "x86gen:43"});
                    emit gp (A.OPER { assem = "\tidiv `s0"
                                         , src = List.map gpArg [e2', F.EAX]
                                         , dst = [F.EAX, F.EDX]
                                         , jump = NONE
                                         , doc = "x86gen:44"});
                    emit gp (moveInstr r F.EAX "45")
                end)
		  
          | munchExp (T.FLOATBINOP (T.DIV,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n1)), s1),
				T.MEM (T.INTBINOP (T.PLUS, e2, T.CONST (T.INT n2)), s2))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, " ^ formatPtr s1 ^ " [`s0 + " ^ int n1 ^ "]"
							 , src = gpArg e1'
							 , dst = r
							 , doc = "x86gen:41,1"});
				emit sse (A.OPER { assem = "\tdivss `d0, " ^ formatPtr s2 ^ " [`s1 + " ^ int n2 ^ "]"
							 , src = [sseArg r, gpArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,2"})
			end)
          | munchExp (T.FLOATBINOP (T.DIV,
				e1,
				T.MEM (T.INTBINOP (T.PLUS, e2, T.CONST (T.INT n)), s))) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e1'
							 , dst = r
							 , doc = "x86gen:41,1"});
				emit sse (A.OPER { assem = "\tdivss `d0, " ^ formatPtr s ^ " [`s1 + " ^ int n ^ "]"
							 , src = [sseArg r, gpArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,2"})
			end)
		  | munchExp (T.FLOATBINOP (T.DIV,
				T.MEM (T.INTBINOP (T.PLUS, e1, T.CONST (T.INT n)), s),
				e2)) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, " ^ formatPtr s ^ " [`s0 + " ^ int n ^ "]"
							 , src = gpArg e1'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\tdivss `d0, `s1"
							 , src = [sseArg r, sseArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)
		  | munchExp (T.FLOATBINOP (T.DIV,
				e1,
				e2)) =
			result (fn r =>
			let
				val e1' = munchExp e1;
				val e2' = munchExp e2;
			in
				emit sse (A.MOVE { assem = "\tmovss `d0, `s0"
							 , src = sseArg e1'
							 , dst = r
							 , doc = "x86gen:41,3"});
				emit sse (A.OPER { assem = "\tdivss `d0, `s1"
							 , src = [sseArg r, sseArg e2']
							 , dst = [r]
							 , jump = NONE
							 , doc = "x86gen:41,4"})
			end)

          (* AND *)
          | munchExp (T.INTBINOP (T.AND, e1, T.CONST (T.INT i))) =
            result (fn r =>
                let
                   val e = munchExp e1
                in
                    emit gp (moveInstr r e "46");
                    emit gp (A.OPER { assem = "\tand `d0, " ^ int i
                                  , src = [gpArg r]
                                  , dst = [r]
                                  , jump = NONE
                                  , doc = "x86gen:47"})
                end)
          | munchExp (T.INTBINOP (T.AND, T.CONST (T.INT i), e1)) =
            result (fn r =>
                let
                   val e = munchExp e1
                in
                    emit gp (moveInstr r e "48");
                    emit gp (A.OPER { assem = "\tand `d0, " ^ int i
                                  , src = [gpArg r]
                                  , dst = [r]
                                  , jump = NONE
                                  , doc = "x86gen:49"})
                end)
          | munchExp (T.INTBINOP (T.AND, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
                     emit gp (moveInstr r e1' "50");
                     emit gp (A.OPER { assem = "\tand `d0, `s1"
                                   , src = List.map gpArg [r, e2']
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:51"})
                end)
            

          (* OR *)
          | munchExp (T.INTBINOP (T.OR, e1, T.CONST (T.INT i))) =
            result (fn r =>
                let
                   val e = munchExp e1
                in
                    emit gp (moveInstr r e "52");
                    emit gp (A.OPER { assem = "\tor `d0, " ^ int i
                                  , src = [gpArg r]
                                  , dst = [r]
                                  , jump = NONE
                                  , doc = "x86gen:53"})
                end)
          | munchExp (T.INTBINOP (T.OR, T.CONST (T.INT i), e1)) =
            result (fn r =>
                let
                   val e = munchExp e1
                in
                    emit gp (moveInstr r e "54");
                    emit gp (A.OPER { assem = "\tor `d0, " ^ int i
                                  , src = [gpArg r]
                                  , dst = [r]
                                  , jump = NONE
                                  , doc = "x86gen:55"})
                end)
          | munchExp (T.INTBINOP (T.OR, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
                     emit gp (moveInstr r e1' "56");
                     emit gp (A.OPER { assem = "\tor `d0, `s1"
                                   , src = [gpArg r, gpArg e2']
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:57"})
                end)
          | munchExp (T.INTBINOP (T.XOR, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
                     emit gp (moveInstr r e1' "58");
                     emit gp (A.OPER { assem = "\txor `d0, `s1"
                                   , src = List.map gpArg [r, e2']
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:59"})
                end)
          | munchExp (T.INTBINOP (T.BEQ, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
				   val r' = forceSize T.BYTE (Tm.newtemp ())
                in
					emit gp (compare e1' e2' "60");
					emit gp (zero r' "71");
                    emit gp (A.OPER { assem = "\tsete `d0"
                                   , src = []
                                   , dst = [r']
                                   , jump = NONE
                                   , doc = "x86gen:61"});
					emit gp (moveZeroExtended r r' "62")
                end)
          | munchExp (T.INTBINOP (T.BNEQ, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
				   val r' = forceSize T.BYTE (Tm.newtemp ())
                in
					emit gp (compare e1' e2' "62");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetne `d0"
                                   , src = []
                                   , dst = [r']
                                   , jump = NONE
                                   , doc = "x86gen:63"});
					emit gp (moveZeroExtended r r' "62")
                end)
          | munchExp (T.INTBINOP (T.BLT, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
				   val r' = forceSize T.BYTE (Tm.newtemp ())
                in
					emit gp (compare e1' e2' "64");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetl `d0"
                                   , src = []
                                   , dst = [r']
                                   , jump = NONE
                                   , doc = "x86gen:65"});
					emit gp (moveZeroExtended r r' "62")
                end)
          | munchExp (T.INTBINOP (T.BGT, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
				   val r' = forceSize T.BYTE (Tm.newtemp ())
                in
					emit gp (compare e1' e2' "66");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetg `d0"
                                   , src = []
                                   , dst = [r']
                                   , jump = NONE
                                   , doc = "x86gen:67"});
					emit gp (moveZeroExtended r r' "62")
                end)
          | munchExp (T.INTBINOP (T.BLE, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
				   val r' = forceSize T.BYTE (Tm.newtemp ())
                in
					emit gp (compare e1' e2' "68");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetle `d0"
                                   , src = []
                                   , dst = [r']
                                   , jump = NONE
                                   , doc = "x86gen:69"});
					emit gp (moveZeroExtended r r' "62")
                end)
          | munchExp (T.INTBINOP (T.BGE, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
				   val r' = forceSize T.BYTE (Tm.newtemp ())
                in
					emit gp (compare e1' e2' "70");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetge `d0"
                                   , src = []
                                   , dst = [r']
                                   , jump = NONE
                                   , doc = "x86gen:71"});
					emit gp (moveZeroExtended r r' "62")
                end)
		  
		  (* If no match, complain *)
		  | munchExp (T.INTBINOP (_, _, _)) = raise (Fail "Unexpected T.INTBINOP in IR")
		  
		  | munchExp (T.FLOATBINOP (T.BEQ, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
					emit sse (compareSSE e1' e2' "71,1");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsete `d0"
                                   , src = []
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:71,2"})
                end)
		  | munchExp (T.FLOATBINOP (T.BNEQ, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
					emit sse (compareSSE e1' e2' "71,3");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetne `d0"
                                   , src = []
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:71,4"})
                end)
		  | munchExp (T.FLOATBINOP (T.BGT, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
					emit sse (compareSSE e1' e2' "71,5");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetg `d0"
                                   , src = []
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:71,6"})
                end)
		  | munchExp (T.FLOATBINOP (T.BLT, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
					emit sse (compareSSE e1' e2' "71,7");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetl `d0"
                                   , src = []
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:71,8"})
                end)
		  | munchExp (T.FLOATBINOP (T.BLE, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
					emit sse (compareSSE e1' e2' "71,9");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetle `d0"
                                   , src = []
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:71,10"})
                end)
		  | munchExp (T.FLOATBINOP (T.BGE, e1, e2)) =
            result (fn r =>
                let
                   val e1' = munchExp e1
                   val e2' = munchExp e2
                in
					emit sse (compareSSE e1' e2' "71,11");
					emit gp (zero r "71");
                    emit gp (A.OPER { assem = "\tsetge `d0"
                                   , src = []
                                   , dst = [r]
                                   , jump = NONE
                                   , doc = "x86gen:71,12"})
                end)
		  
		  | munchExp (T.FLOATBINOP (_, _, _)) = raise (Fail "Unexpected T.FLOATBINOP in IR")


          (* Other constructs *)
          | munchExp (T.TEMP t) = t
		  
          | munchExp (T.ESEQ (s, e)) = (munchStm s; munchExp e)
		  
          | munchExp (T.NAME label) =
            result (fn r => 
                    emit gp (A.OPER { assem = "\tmov `d0, offset " ^ S.name label
                                       , src = []
                                       , dst = [gpArg r]
                                       , jump = NONE
                                       , doc = "x86gen:58"}))
		  
          | munchExp (T.CONST (T.INT n)) =
			result (fn r => emit gp (moveConstIntInstr r n "59"))
		  | munchExp (T.CONST (T.FLOAT f)) =
			result (fn r => emit sse (moveConstFloatInstr r f "60"))
		  | munchExp (T.CONST (T.DEFINE s)) =
			result (fn r =>
				emit gp (A.OPER { assem = "\tmov `d0, " ^ s
							 , src = []
							 , dst = [gpArg r]
							 , jump = NONE
							 , doc = "x86gen:61"}))
		  
		  | munchExp (T.CALL _) = raise (Fail "Unexpected dangling call in IR")
    in
		munchStm stm;
		
        (rev (!ilist), !regClassMap, !frags')
    end

end (* X86Gen *)


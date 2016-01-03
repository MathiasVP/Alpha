structure RegAlloc: REG_ALLOC =
struct
	structure Frame = X86Frame
	structure MG = MakeGraph
	structure L = Liveness
	structure C = Color
	
	type allocation = Frame.register Temp.Table.table
	
	fun rewrite (instrs, spills, frame, regClassMap) =
		let
			fun spill (temp, (instrs, regClassMap)) =
				let
					val access = Frame.allocLocal frame true
					val accessExp = Frame.exp access (Tree.TEMP Frame.FP)
					
					fun moveInsn (dst, src, regClassMap) =
						let
							val (instrs, regClassMap', _) =
								X86Gen.codegen frame (Tree.MOVE (dst, src)) regClassMap []
						in
							(instrs,
							 Temp.Table.unionWith (fn (regs1, regs2) =>
								IntBinarySet.intersection (regs1, regs2)
							 ) (regClassMap, regClassMap'))
						end
					
					fun storeInsn regClassMap temp = moveInsn (accessExp, Tree.TEMP temp, regClassMap)
					fun fetchInsn regClassMap temp = moveInsn (Tree.TEMP temp, accessExp, regClassMap)

					fun replace newTemp temp' =
						if temp = temp' then newTemp else temp'

					fun transform regClassMap insnBuilder temps =
						if List.exists (fn t => t = temp) temps then
							let
								val t = Temp.newtemp ()
								val (instrs, regClassMap') = insnBuilder regClassMap t
							in
								(instrs, map (replace t) temps, regClassMap)
							end
						else
							([], temps, regClassMap)

					fun rewriteInsn (Assem.OPER {assem, dst, src, jump, doc}, regClassMap) =
						let
							val (pre, src', regClassMap') = transform regClassMap fetchInsn src
							val (post, dst', regClassMap'') = transform regClassMap storeInsn dst
						in
							(pre @
								[Assem.OPER { assem = assem
											  , dst = dst'
											  , src = src'
											  , jump = jump
											  , doc = doc}]
							@ post, regClassMap)
						end
					  | rewriteInsn (Assem.MOVE {assem, src, dst, doc}, regClassMap) =
						let
							val (pre, [src'], regClassMap') = transform regClassMap fetchInsn [src]
							val (post, [dst'], regClassMap'') = transform regClassMap storeInsn [dst]
						in
							(pre @
								[Assem.MOVE	{ assem = assem
											, dst = dst'
											, src = src'
											, doc = doc}]
							@ post, regClassMap)
						end
					  | rewriteInsn (instr, regClassMap) = ([instr], regClassMap)
				in
					List.foldl (fn (instr, (instrs, regClassMap)) =>
						let
							val (instrs', regClassMap') = rewriteInsn (instr, regClassMap)
						in
							(instrs @ instrs', regClassMap)
						end
					) ([], regClassMap) instrs
			end
		in
			List.foldl spill (instrs, regClassMap) spills
		end
	
	fun alloc (instrs, frame, regClassMap) =
		let
			val (flow as Flow.FGRAPH {control, def, use, ismove}, nodes) = MG.instrs2graph instrs;
			val (igraph as L.IGRAPH {graph, tnode, gtemp, moves}, liveout) = L.interferenceGraph flow regClassMap;
			
			fun spillCost node =
				let
					val temp = gtemp node

					fun getOccurences node =
						let
							val uses = case Graph.Table.look (use, node) of
								NONE => raise Fail "Node not found in use[n]"
							  | SOME uses => uses
							val defs = case Graph.Table.look (def, node) of
								NONE => raise Fail "Node not found in def[n]"
							  | SOME defs => defs
							  
							val useCount =	if Temp.Set.member (uses, temp) then
												1
											else 0
							val defCount =	if Temp.Set.member (defs, temp) then
												1
											else 0
						in
							useCount + defCount
						end

					val occurences = List.foldl (fn (node, total) =>
										getOccurences node + total)
										0 nodes

					val degree = List.length (Graph.adj node)
				in
					(Real.fromInt occurences) / (Real.fromInt degree)
				end
			
			val (allocation, spills) = C.color { interference = igraph
					, initial = Frame.tempMap
					, spillCost = spillCost
					, registers = Frame.registers}
		in
			if List.null spills then
				(instrs, allocation)
			else
				let
					val (instrs', regClassMap') = rewrite (instrs, spills, frame, regClassMap)
				in
					alloc (instrs', frame, regClassMap')
				end
		end
end
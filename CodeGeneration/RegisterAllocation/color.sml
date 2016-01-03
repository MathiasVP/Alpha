structure Color : COLOR =
struct	
	structure Frame = X86Frame
	structure Tm = Temp
	structure L = Liveness
	structure RS = BinarySetFn (type ord_key = string
								val compare = String.compare)
	
	type allocation = Frame.register Temp.Table.table
	
	structure NodeWL = WorkLists(structure Set = Graph.Set)
	structure MoveSet = WorkLists(structure Set =
		BinarySetFn (struct
			type ord_key = NodeWL.item * NodeWL.item
			fun compare ((n1, n2), (m1, m2)) =
				let
					val r1 = NodeWL.Set.Key.compare (n1, m1)
					val r2 = NodeWL.Set.Key.compare (n2, m2)
				in
					if r1 = General.EQUAL then r2
					else r1
				end
		end))
	
	structure Id =
		struct
			val precolored = NodeWL.newId "precolored";
			val initial = NodeWL.newId "initial";
			val simplify = NodeWL.newId "simplify";
			val freeze = NodeWL.newId "freeze";
			val spill = NodeWL.newId "spill";
			val spilledNodes = NodeWL.newId "spilledNodes";
			val coalescedNodes = NodeWL.newId "coalescedNodes";
			val coloredNodes = NodeWL.newId "coloredNodes";
			val select = NodeWL.newId "select";
			
			val coalescedMoves = MoveSet.newId "coalescedMoves"
			val constrainedMoves = MoveSet.newId "constrainedMoves"
			val frozenMoves = MoveSet.newId "frozenMoves"
			val worklistMoves = MoveSet.newId "worklistMoves"
			val activeMoves = MoveSet.newId "activeMoves"
		end
		
	fun toNodeSet list = Graph.Set.addList (Graph.Set.empty, list)
	fun toNodePairSet list = MoveSet.Set.addList (MoveSet.Set.empty, list)
	
	fun color { interference = L.IGRAPH {graph, tnode, gtemp, moves},
				initial, spillCost, registers} =
		let
		
		val k = List.length registers
		val (precolored', uncolored') = List.partition (fn node =>
			case Tm.Table.look (initial, gtemp node) of
				NONE => false
			  | SOME _ => true) (Graph.nodes graph);

		val precolored = toNodeSet precolored'
		val uncolored = toNodeSet uncolored'
		fun isPrecolored n =
			NodeWL.Set.exists (fn n' => Graph.eq (n, n')) precolored
			
		fun adjacent worklists n =
			let
				val adj = toNodeSet (Graph.adj n)
				val select = NodeWL.asSet worklists Id.select
				val coalescedNodes = NodeWL.asSet worklists Id.coalescedNodes
			in
				NodeWL.Set.difference (adj, NodeWL.Set.union (select, coalescedNodes))
			end

		fun nodeMoves movesets moves n =
			let
				val moveList = case Graph.Table.look (moves, n) of
					NONE => MoveSet.Set.empty
				  | SOME moves => moves
				  
				val activeMoves = MoveSet.asSet movesets Id.activeMoves
				val worklistMoves = MoveSet.asSet movesets Id.worklistMoves
			in
				MoveSet.Set.intersection (moveList,
					MoveSet.Set.union (activeMoves, worklistMoves))
			end
			
		fun moveRelated movesets moves n =
			not (MoveSet.Set.isEmpty (nodeMoves movesets moves n))

		fun enableMoves nodes movesets moves =
			Graph.Set.foldl (fn (n, movesets') =>
				let
					val moves' = nodeMoves movesets' moves n
				in
					MoveSet.Set.foldl (fn (n', movesets') =>
						if MoveSet.isMember movesets' Id.activeMoves n' then
							MoveSet.move movesets' Id.activeMoves Id.worklistMoves n'
						else movesets'
					) movesets' moves'
				end
			) movesets nodes
		
		fun decrementDegree moves (n, (worklists, movesets, degrees)) =
			let
				val d = case Graph.Table.look (degrees, n) of
					NONE => raise Fail ("decrementDegree: Degree of node " ^
						(Frame.asStringReg o gtemp) n ^ " not found")
				  | SOME deg => deg
				val degrees' = Graph.Table.enter (degrees, n, if isPrecolored n then d else d - 1)
				
				val (worklist', movesets') =
					if d = k andalso not (isPrecolored n) then
						let
							val moves' = NodeWL.Set.union
								(NodeWL.Set.singleton n, adjacent worklists n)
							val movesets' = enableMoves moves' movesets moves
							val worklist' =
								NodeWL.move worklists Id.spill
									(if moveRelated movesets' moves n then
										Id.freeze
									 else Id.simplify) n
						in
							(worklist', movesets')
						end
					else (worklists, movesets)
			in
				(worklist', movesets', degrees')
			end

		fun simplify worklists movesets degrees alias moves =
			case (NodeWL.asList worklists Id.simplify) of
				[] => (worklists, movesets, degrees, alias, moves)
			  | n :: _ =>
				let
					val worklists' = NodeWL.move
						worklists Id.simplify Id.select n
					val adj = adjacent worklists' n
					val (worklists'', movesets', degrees') =
						Graph.Set.foldl (decrementDegree moves)
						(worklists', movesets, degrees) adj
				in
					(worklists'', movesets', degrees', alias, moves)
				end
				
		fun getAlias worklists alias n =
			let
				val coalescedNodes = NodeWL.asSet worklists Id.coalescedNodes
			in
				if NodeWL.Set.member (coalescedNodes, n) then
					let
						val n' = case Graph.Table.look (alias, n) of
							NONE => raise Fail "Alias of node not found"
						  | SOME n' => n'
					in
						getAlias worklists alias n'
					end
				else n
			end
			
		fun addWorkList worklists movesets degrees moves n =
			let
				val d = case Graph.Table.look (degrees, n) of
					NONE => raise Fail ("addWorkList: Degree of node " ^
						(Frame.asStringReg o gtemp) n ^ " not found")
				  | SOME deg => deg
			in
				if not (isPrecolored n) andalso
					not (moveRelated movesets moves n)
					andalso d < k then
					NodeWL.move worklists Id.freeze Id.simplify n
				else worklists
			end

		fun ok degrees (t, r) =
			let
				val d = case Graph.Table.look (degrees, t) of
				NONE => raise Fail ("ok: Degree of node " ^
					(Frame.asStringReg o gtemp) t ^ " not found")
			  | SOME deg => deg
			in
				d < k orelse
				isPrecolored t orelse
				List.exists (fn n => Graph.eq(n, r)) (Graph.adj t)
			end
			
		fun conservative degrees nodes =
			(NodeWL.Set.foldl (fn (n, k') =>
				case Graph.Table.look (degrees, n) of
					NONE => raise Fail ("conservative: Degree of node " ^
						(Frame.asStringReg o gtemp) n ^ " not found")
				  | SOME deg =>
					if deg >= k then k' + 1 else k'
				) 0 nodes
			) < k
			
		fun combine worklists movesets degrees alias moves u v =
			let
				val worklists' = NodeWL.move worklists
					(if NodeWL.isMember worklists Id.freeze v then
						Id.freeze
					else Id.spill) Id.coalescedNodes v
				
				val alias' = Graph.Table.enter (alias, v, u)
					
				val uMoves = case Graph.Table.look (moves, u) of
					NONE => MoveSet.Set.empty
				  | SOME moves => moves
				  
				val vMoves = case Graph.Table.look (moves, v) of
					NONE => MoveSet.Set.empty
				  | SOME moves => moves
				  
				val moves' = Graph.Table.enter (moves, u, MoveSet.Set.union (uMoves, vMoves))				
				val movesets' = enableMoves (NodeWL.Set.singleton v) movesets moves'
				
				val decrementDegree' = decrementDegree moves'
				val (worklists'', movesets'', degrees') =
					NodeWL.Set.foldl (fn (t, (worklists, movesets, degrees)) =>
						let
							val (degrees', worklists') =
								if not (Graph.eq (t, u)) andalso
								   not (List.exists (fn n => Graph.eq(n, t)) (Graph.adj u)) then
									let
										val dt = case Graph.Table.look (degrees, t) of
											NONE => raise Fail ("Degree of node " ^
												(Frame.asStringReg o gtemp) t ^ " not found")
										  | SOME d => d
										  
										val du = case Graph.Table.look (degrees, u) of
											NONE => raise Fail ("Degree of node " ^
												(Frame.asStringReg o gtemp) u ^ " not found")
										  | SOME d => d
										 
										val dt' = if isPrecolored t then dt else dt+1
										val du' = if isPrecolored u then du else du+1
										
										val degrees' = Graph.Table.enter (degrees, t, dt')
										val degrees'' = Graph.Table.enter (degrees', u, du')
										
										(* Note:
											This is actually NOT described in the book.
											Whenever we add an edge in the graph there's a chance that a node will go
											from being light to being heavy. Note that, as correctly described by
											Appel, we are guaranteed that the colourability of the graph is kept
											since we have passed the Briggs test.
											
											However (!!!) there is a chance that the degree of the node will go
											from being less than k to being equal to k. In that case Appel breaks
											his invariants as described on page 244, and in order to fix this we
											need to move it from simplify (if the node is not move-related) and
											into spill. Similarly if the node is move-related we need to move it
											from freeze and into spill.
										*)
										
										fun move worklists temp =
											if NodeWL.isMember worklists Id.simplify temp then
												NodeWL.move worklists Id.simplify Id.spill temp
											else if NodeWL.isMember worklists Id.freeze temp then
												NodeWL.move worklists Id.freeze Id.spill temp
											else worklists
											
										val worklists' =
											if dt' = k then
												move worklists t
											else worklists
											
										val worklists'' =
											if du' = k then
												move worklists' u
											else worklists'
									in
										Graph.mk_edge {from = t, to = u};
										(degrees'', worklists'')
									end
								else (degrees, worklists)
						in
							decrementDegree' (t, (worklists', movesets, degrees'))
						end
					) (worklists', movesets', degrees) (adjacent worklists' v)

				val udeg = case Graph.Table.look (degrees', u) of
					NONE => raise Fail ("combine: Degree of node " ^
						(Frame.asStringReg o gtemp) u ^ " not found")
				  | SOME deg => deg
				
				val worklists''' =
					if udeg >= k andalso NodeWL.isMember worklists'' Id.freeze u then
						NodeWL.move worklists'' Id.freeze Id.spill u
					else worklists''
			in
				(worklists''', movesets'', degrees', alias', moves')
			end

		fun coalesce worklists movesets degrees alias moves =
			case (MoveSet.asList movesets Id.worklistMoves) of
				[] => (worklists, movesets, degrees, alias, moves)
			  | (n as (x, y)) :: _ =>
				let
					val x' = getAlias worklists alias x
					val y' = getAlias worklists alias y
					val (u, v) =
						if isPrecolored y' then
							(y', x')
						else (x', y')

					val moveTo = MoveSet.move' movesets n Id.worklistMoves
					val (worklists', movesets', degrees', alias', moves') =
						if Graph.eq (u, v) then
							let
								val movesets' = moveTo Id.coalescedMoves
								val worklists' = addWorkList worklists movesets' degrees moves u
							in
								(worklists', movesets', degrees, alias, moves)
							end
						else if isPrecolored v orelse
							List.exists (fn n' => Graph.eq(n', v)) (Graph.adj u) then
							let
								val movesets' = moveTo Id.constrainedMoves
								val worklists' = addWorkList worklists movesets' degrees moves u
								val worklists'' = addWorkList worklists' movesets' degrees moves v
							in
								(worklists'', movesets', degrees, alias, moves)
							end
						else if (isPrecolored u andalso
							List.all (fn t => ok degrees (t, u)) (NodeWL.Set.listItems (adjacent worklists v)))
							orelse
							(not (isPrecolored u) andalso
							conservative degrees (NodeWL.Set.union (adjacent worklists u, adjacent worklists v)))
							then
								let
									val movesets' = moveTo Id.coalescedMoves
									val (worklists', movesets'', degrees', alias', moves') =
										combine worklists movesets' degrees alias moves u v
									val worklists'' =
										addWorkList worklists' movesets'' degrees' moves' u
								in
									(worklists'', movesets'', degrees', alias', moves')
								end
						else
							(worklists, moveTo Id.activeMoves, degrees, alias, moves)
				in
					(worklists', movesets', degrees', alias', moves')
				end
				
			fun freezeMoves worklists movesets degrees alias moves u =
				let
					val (worklists', movesets') =
						MoveSet.Set.foldl (fn (m as (x, y), (worklists, movesets)) =>
							let
								val x' = getAlias worklists alias x
								val y' = getAlias worklists alias y
								val v = if Graph.eq (y', getAlias worklists alias u) then x' else y'
								
								val movesets' = MoveSet.move movesets
									Id.activeMoves Id.frozenMoves m
									
								val degv = case Graph.Table.look (degrees, v) of
									NONE => raise Fail ("freezeMoves: Degree of node " ^
										(Frame.asStringReg o gtemp) v ^ " not found")
								  | SOME deg => deg
								  
								val worklists' =
									if not (moveRelated movesets' moves v) andalso degv < k then
										NodeWL.move worklists Id.freeze Id.simplify v
									else worklists
							in
								(worklists', movesets')
							end) (worklists, movesets) (nodeMoves movesets moves u)
				in
					(worklists', movesets', degrees, alias, moves)
				end
		
			fun freeze worklists movesets degrees alias moves =
				case NodeWL.asList worklists Id.freeze of
					[] => (worklists, movesets, degrees, alias, moves)
				  | u :: _ =>
					let
						val worklists' = NodeWL.move worklists
							Id.freeze Id.simplify u
					in
						freezeMoves worklists' movesets degrees alias moves u
					end
					
			fun selectSpill worklists movesets degrees alias moves =
				let
					fun min [] = raise Fail "Cannot apply min on empty list"
					  | min (first :: rest) =
						let
							val (item, _) =
								List.foldl (fn (item, (minItem, minVal)) =>
									let
										val itemVal = (spillCost item):real
									in
										if itemVal < minVal then
											(item, itemVal)
										else
											(minItem, minVal)
									end
								) (first, spillCost first) rest
						in
							item
						end
					val m = min (NodeWL.asList worklists Id.spill)
					val worklists' = NodeWL.move worklists Id.spill Id.simplify m
				in
					freezeMoves worklists' movesets degrees alias moves m
				end
				
			fun loop (worklists, movesets, degrees, alias, moves) =
				if not (NodeWL.isEmpty worklists Id.simplify) then
					loop (simplify worklists movesets degrees alias moves)
					
				else if not (MoveSet.isEmpty movesets Id.worklistMoves) then
					loop (coalesce worklists movesets degrees alias moves)
						
				else if not (NodeWL.isEmpty worklists Id.freeze) then
					loop (freeze worklists movesets degrees alias moves)
						
				else if not (NodeWL.isEmpty worklists Id.spill) then
					loop (selectSpill worklists movesets degrees alias moves)
						
				else (worklists, movesets, degrees, alias, moves)
				
			val worklists = NodeWL.newLists [
					(Id.precolored, NodeWL.Set precolored),
					(Id.initial, NodeWL.Set uncolored),
					(Id.simplify, NodeWL.Set (toNodeSet [])),
					(Id.freeze, NodeWL.Set (toNodeSet [])),
					(Id.spill, NodeWL.Set (toNodeSet [])),
					(Id.spilledNodes, NodeWL.Set (toNodeSet [])),
					(Id.coalescedNodes, NodeWL.Set (toNodeSet [])),
					(Id.coloredNodes, NodeWL.Set (toNodeSet [])),
					(Id.select, NodeWL.List [])]
		
			val movesets = MoveSet.newLists [
						(Id.coalescedMoves, MoveSet.Set (toNodePairSet [])),
						(Id.constrainedMoves, MoveSet.Set (toNodePairSet [])),
						(Id.frozenMoves, MoveSet.Set (toNodePairSet [])),
						(Id.worklistMoves, MoveSet.Set (toNodePairSet moves)),
						(Id.activeMoves, MoveSet.Set (toNodePairSet []))]
					
			val moves = List.foldl (fn (m as (a, b), moves) =>
					let
						val moves' = case Graph.Table.look (moves, a) of
							NONE =>
								Graph.Table.enter (moves, a, MoveSet.Set.singleton m)
						  | SOME aMoves =>
								Graph.Table.enter (moves, a, MoveSet.Set.add (aMoves, m))
								
						val moves'' = case Graph.Table.look (moves', b) of
							NONE =>
								Graph.Table.enter (moves', b, MoveSet.Set.singleton m)
						  | SOME bMoves =>
								Graph.Table.enter (moves', b, MoveSet.Set.add (bMoves, m))
					in
						moves''
					end
				) Graph.Table.empty moves
					
			val degrees = List.foldl (fn ((n, deg), degrees) =>
					Graph.Table.enter (degrees, n, deg)
				) Graph.Table.empty
				(map (fn node =>
					(node, List.length (Graph.adj node))
				) (Graph.nodes graph))
				
			val alias = Graph.Table.empty
				
			val worklists = Graph.Set.foldl (fn (n, worklists) =>
			let
				val moveTo = NodeWL.move' worklists n Id.initial
				val degree = case Graph.Table.look (degrees, n) of
					NONE => raise Fail "Degree of node not found"
				  | SOME deg => deg
			in
				if degree >= k then
					moveTo Id.spill
				else if moveRelated movesets moves n then
					moveTo Id.freeze
				else
					moveTo Id.simplify
			end) worklists (NodeWL.asSet worklists Id.initial)
				
			val (worklists, _, _, alias, _) =
				loop (worklists, movesets, degrees, alias, moves)
				
			val colors = RS.addList (RS.empty, registers)
			fun assignColors worklists alias =
			let
				fun makeInitNodeColor [] colors = colors
				  | makeInitNodeColor ((reg, c)::rest) colors =
					Graph.Table.enter (makeInitNodeColor rest colors, tnode reg, c)
					
				val initNodeColor = makeInitNodeColor
					(Temp.Table.entries initial) Graph.Table.empty
					
				val (worklists, nodeColor, tempColor) =
					List.foldl (fn (n, (worklists, nodeColor, tempColor)) =>
					let
						val usedColors = RS.addList (
							RS.empty,
							List.mapPartial (fn w =>
								Graph.Table.look (nodeColor, getAlias worklists alias w)
							) (Graph.adj n))
						val okColors = RS.difference (colors, usedColors)
					in
						case RS.listItems okColors of
							[] =>
							(NodeWL.move worklists Id.select Id.spilledNodes n,
							 nodeColor,
							 tempColor)
						  | c :: _ =>
							(NodeWL.move worklists Id.select Id.coloredNodes n,
							 Graph.Table.enter (nodeColor, n, c),
							 Temp.Table.enter (tempColor, gtemp n, c))
					end
					) (worklists, initNodeColor, initial) (NodeWL.asList worklists Id.select)
				
				
				
				val (_, tempColor') = List.foldl (fn (n, (nodeColor, tempColor)) =>
						let
							val n' = getAlias worklists alias n
							val color = case Graph.Table.look (nodeColor, n') of
								NONE => raise Fail ("Color for node " ^
									(Frame.asStringReg o gtemp) n' ^ "not found")
							  | SOME c => c
						in
							(Graph.Table.enter (nodeColor, n, color),
							 Temp.Table.enter (tempColor, gtemp n, color))
						end
					) (nodeColor, tempColor) (NodeWL.asList worklists Id.coalescedNodes)
			in
				(worklists, tempColor')
			end
			
			val (worklists, allocation) = assignColors worklists alias
			val spills = List.map gtemp (NodeWL.asList worklists Id.spilledNodes)
		in
			(allocation, spills)
		end
end
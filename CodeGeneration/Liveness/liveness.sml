structure Liveness :
sig
  datatype igraph =
    IGRAPH of {graph: Graph.graph,
               tnode: Temp.temp -> Graph.node,
               gtemp: Graph.node -> Temp.temp,
               moves: (Graph.node * Graph.node) list}

  structure Frame : FRAME
			   
  val interferenceGraph :
      Flow.flowgraph -> IntBinarySet.set Temp.Table.table -> igraph * (Flow.Graph.node -> Temp.temp list)

  val show : TextIO.outstream * igraph -> unit
end =
struct

structure Frame = X86Frame
structure FT = Flow.Graph.Table

datatype igraph = IGRAPH of {graph: Graph.graph,
                             tnode: Temp.temp -> Graph.node,
                             gtemp: Graph.node -> Temp.temp,
                             moves: (Graph.node * Graph.node) list}
							 
fun calcLiveOut (Flow.FGRAPH {control, def, use, ismove}) =
    let
		val nodes = Flow.Graph.nodes control
    
		fun build ([], livein, liveout) = (livein, liveout)
		  | build (node :: nodes, livein, liveout) =
			let
				val def = case FT.look (def, node) of
					NONE => raise Fail "No def[n] for node"
				  | SOME temps => temps
				  
				val use = case FT.look (use, node) of
					NONE => raise Fail "No use[n] for node"
				  | SOME temps => temps
				  
				val out = case FT.look (liveout, node) of
					NONE => Temp.Set.empty
				  | SOME temps => (temps:Temp.Set.set)
				  
				val in' = Temp.Set.union (use, Temp.Set.difference (out, def))
				val out' = List.foldl (fn (s, liveout') =>
					let
						val succIn = case FT.look (livein, s) of
							NONE => Temp.Set.empty
						  | SOME temps => temps
					in
						Temp.Set.union (liveout', succIn)
					end) Temp.Set.empty (Flow.Graph.succ node)
				
				val livein' = FT.enter (livein, node, in')
				val liveout' = FT.enter (liveout, node, out')
			in
				build (nodes, livein', liveout')
			end
			
		fun fixpoint (livein, liveout) =
			let
				fun equalTables (t1, t2) =
					FT.collate (fn (set1, set2) =>
						Temp.Set.compare (set1, set2)) (t1, t2) = EQUAL
			
				val (livein', liveout') = build (nodes, livein, liveout)
			in
				if(equalTables (livein, livein') andalso equalTables (liveout, liveout')) then
					liveout'
				else
					fixpoint (livein', liveout')
			end
	in
		fixpoint (build (nodes, FT.empty, FT.empty))
    end
							 
fun interferenceGraph (flowgraph as Flow.FGRAPH {control, def, use, ismove}) regClassMap =
    let
		val nodes = Flow.Graph.nodes control
		
		val allTemps = List.foldl (fn (n, temps) => 
			let
				val defs = case FT.look (def, n) of
					NONE => raise Fail "def of node not found in flow graph"
				  | SOME temps => temps
				val uses = case FT.look (use, n) of
					NONE => raise Fail "uses of node not found in flow graph"
				  | SOME temps => temps
			in
				Temp.Set.union (temps, Temp.Set.union (defs, uses))
			end) Temp.Set.empty nodes
	  
		val igraph = Graph.newGraph ();
		
		(* Create table mapping node -> temp and temp -> node *)
		val (n2tMap, t2nMap) = Temp.Set.foldl (fn (temp, (n2t, t2n)) =>
			let
				val n = Graph.newNode igraph
			in
				(Graph.Table.enter (n2t, n, temp),
				Temp.Table.enter (t2n, temp, n))
			end) (Graph.Table.empty, Temp.Table.empty)
				(Temp.Set.addList (allTemps, [Frame.EAX, Frame.EBX, Frame.ECX,
				 Frame.EDX, Frame.ESI, Frame.EDI,
				 Frame.XMM0, Frame.XMM1, Frame.XMM2,
				 Frame.XMM3, Frame.XMM4, Frame.XMM5,
				 Frame.XMM6, Frame.XMM7]))

		fun nodeToTemp node =
			case FT.look (n2tMap, node) of
				NONE => raise Fail "Node not found in node -> temp table"
			  | SOME temp => temp
		fun tempToNode temp =
			case Temp.Table.look (t2nMap, temp) of
				NONE => raise Fail "Temporary not found in temp -> node table"
			  | SOME node => node
		
		val liveoutMap = calcLiveOut flowgraph
		fun liveout node = Temp.Set.listItems (case FT.look (liveoutMap, node) of
			NONE => raise Fail "out[n] of node not found"
		  | SOME temps => temps)
		  
		fun isMove node =
			case FT.look (ismove, node) of
				NONE => raise Fail "Node not found in is-move map"
			  | SOME b => b
		
		fun isConnected a b =
			List.exists (fn n => Graph.eq (n, b)) (Graph.adj a)
		
		val moves = List.foldl (fn (node, moves) =>
			if isMove node then
				let
					val [dst] = Temp.Set.listItems (case FT.look (def, node) of
						NONE => raise Fail "Node not found in def[n]"
					  | SOME node => node)
					val [src] = Temp.Set.listItems (case FT.look (use, node) of
						NONE => raise Fail "Node not found in use[n]"
					  | SOME node => node)
					val dstNode = tempToNode dst
					val srcNode = tempToNode src
				in
					if List.exists (fn (a, b) =>
						Graph.eq (a, dstNode) andalso Graph.eq(b, srcNode) orelse
						Graph.eq (a, srcNode) andalso Graph.eq(b, dstNode)
					) moves then moves
					else (dstNode, srcNode)::moves
				end
			else moves) [] nodes
			
		fun addEdges node =
			let
				val defs =
					case FT.look (def, node) of
						NONE => raise Fail "Not not found in def[n]"
					  | SOME temps => temps
				val uses =
					case FT.look (use, node) of
						NONE => raise Fail "Not not found in use[n]"
				  | SOME temps => temps
			in
				if isMove node then
					let
						val _ =
							if Temp.Set.numItems uses <> 1 orelse
								Temp.Set.numItems defs <> 1 then
								raise Fail ("Assertion failed: " ^
								"Expected number of defs and uses for move to be 1")
							else ()
						val a = (List.hd o Temp.Set.listItems) defs
						val c = (List.last o Temp.Set.listItems) uses
						val out = liveout node
						val aNode = tempToNode a
					in
						List.app (fn b =>
							let
								val bNode = tempToNode b
							in
								if b <> c andalso a <> b andalso
									not (isConnected aNode bNode) then
									Graph.mk_edge { from = aNode
												  , to = bNode}
								else ()
							end
						) out
					end
				else
					Temp.Set.app (fn a =>
						let val aNode = tempToNode a
						in
							List.app (fn b =>
								let
									val bNode = tempToNode b
								in
									if a <> b andalso not (isConnected aNode bNode) then
										Graph.mk_edge { from = aNode
													  , to = bNode}
									else ()
								end
							) (liveout node)
						end
					) defs
			end

		val _ = List.app addEdges nodes
		
		local
			val allregs = IntBinarySet.addList (IntBinarySet.empty,
				[Frame.EAX, Frame.EBX, Frame.ECX,
				 Frame.EDX, Frame.ESI, Frame.EDI, Frame.FP, Frame.SP,
				 Frame.XMM0, Frame.XMM1, Frame.XMM2,
				 Frame.XMM3, Frame.XMM4, Frame.XMM5,
				 Frame.XMM6, Frame.XMM7])
		in
			fun addRegisterConstraints node =
			let
				val defs = case FT.look (def, node) of
					 NONE => raise Fail "Node not found in def[n]"
				   | SOME temps => temps
				val uses = case FT.look (use, node) of
					 NONE => raise Fail "Node not found in use[n]"
				   | SOME temps => temps
			in
				Temp.Set.app (fn a =>
					let
						val regs = case Temp.Table.look (regClassMap, a) of
							NONE => IntBinarySet.empty
						  | SOME regs => IntBinarySet.difference (allregs, regs)
						val aNode = tempToNode a
					in
						IntBinarySet.app (fn reg =>
							let
								val regNode = tempToNode reg
							in
								if not (Graph.eq (aNode, regNode)) andalso
									not (isConnected aNode regNode) then
										Graph.mk_edge {from = aNode, to = regNode}
								else ()
							end
						) regs
					end
				) (Temp.Set.union (defs, uses))
			end
			
			val _ = IntBinarySet.app (fn reg =>
				let val regNode = tempToNode reg
				in IntBinarySet.app (fn reg2 =>
					let val reg2Node = tempToNode reg2
					in if reg <> reg2 andalso
							not (isConnected regNode reg2Node) then
								Graph.mk_edge {from = regNode, to = reg2Node}
						else ()
					end
				) allregs
				end
			) allregs
		end

		val _ = List.app addRegisterConstraints nodes
		
		val graph = IGRAPH {graph=igraph,
               tnode=tempToNode,
               gtemp=nodeToTemp,
               moves=moves}
    in
      (graph, liveout)
    end
	
and show (out, (IGRAPH {graph, tnode, gtemp, moves})) =
	let
		val nodes = Flow.Graph.nodes graph
		val nodeToStr = Frame.asStringReg o gtemp
	in
		List.app (fn node =>
			TextIO.output (out,
				nodeToStr node ^ " -> " ^
				String.concatWith ", " (List.map nodeToStr (Graph.adj node)) ^ "\n")
		) nodes
	end
end
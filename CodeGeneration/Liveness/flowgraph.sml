structure Flow =
struct
	structure Graph = Graph
	structure Frame: FRAME = X86Frame
    datatype flowgraph = FGRAPH of {control: Graph.graph,
				    def: Temp.Set.set Graph.Table.table,
				    use: Temp.Set.set Graph.Table.table,
				    ismove: bool Graph.Table.table}

  (* Note:  any "use" within the block is assumed to be BEFORE a "def" 
        of the same variable.  If there is a def(x) followed by use(x)
       in the same block, do not mention the use in this data structure,
       mention only the def.

     More generally:
       If there are any nonzero number of defs, mention def(x).
       If there are any nonzero number of uses BEFORE THE FIRST DEF,
           mention use(x).

     For any node in the graph,  
           Graph.Table.look(def,node) = SOME(def-list)
           Graph.Table.look(use,node) = SOME(use-list)
   *)

	fun asString (FGRAPH {control, def, use, ismove}) =
		let
			fun nodeToString node =
				(Graph.nodename node) ^
				" [" ^
				(String.concatWith " " (map Frame.asStringReg
					(Temp.Set.listItems (valOf (Graph.Table.look (def, node)))))) ^
				" <- " ^
					(String.concatWith " " (map Frame.asStringReg
						(Temp.Set.listItems (valOf (Graph.Table.look (use, node)))))) ^
				"]"
		in
        app (fn n =>
			print (nodeToString n ^ ": " ^
				(String.concatWith ", " (map Graph.nodename (Graph.succ n))) ^ "\n"))
			(Graph.nodes control)
      end
   
end
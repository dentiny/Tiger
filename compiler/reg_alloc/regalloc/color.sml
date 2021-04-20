(*signature COLOR = 
sig	
  structure Frame: FRAME
	type allocation = Frame.register Temp.Table.table

	val color: {interference: Liveness.igraph,
							initial: allocation,
							spillCost: unit Graph.node -> int,
							registers: Frame.register list}
              -> 	allocation * Temp.temp list
end*)

structure Color : COLOR = 
struct
	structure Frame = MipsFrame
	structure F = Frame
	structure Tab = Temp.Table
	structure G = Flow.Graph
	type allocation = F.register Tab.table

	structure S = RedBlackSetFn(
		struct
			type ord_key = string
			val compare = String.compare
		end)

	fun errorMsg msg = ErrorMsg.error 0 ("Compiler error: " ^ msg) 

	fun getMoveCount (curNode, []) = 0
		| getMoveCount (curNode: unit G.node,
										(src, dst) :: (l: (unit G.node * unit G.node) list)) =
			if (G.getNodeID(curNode) = G.getNodeID(src) orelse G.getNodeID(curNode) = G.getNodeID(dst)) then 1 + getMoveCount(curNode, l)
			else getMoveCount(curNode, l)

	fun getSimplifiedNode([], _, _, _) = NONE
		| getSimplifiedNode(curNode :: l,
												reg_number: int,
												moveList: (unit G.node * unit G.node) list,
												initial: allocation) =
			let
				val degree = G.outDegree(curNode) + getMoveCount(curNode, moveList)
				(*val _ = print ("[degree]" ^ Int.toString degree ^ "\n") *)
				val curNodeId = G.getNodeID(curNode)
				val is_precolored = isSome(Tab.look(initial, curNodeId))
			in
				if (degree < reg_number andalso (not(is_precolored))) then SOME(curNode)
				else getSimplifiedNode(l, reg_number, moveList, initial)
			end

	fun allocColor (_, [], neighRegs) = NONE (* no register to allocate *)
		| allocColor (curNode: unit G.node,
									curReg :: (registers: Frame.register list),
									neighRegs) =
			if S.member(neighRegs, curReg) 
			then allocColor(curNode, registers, neighRegs)
			else SOME(curReg)

	fun color {interference as Liveness.IGRAPH{graph, tnode, gtemp, moves},
							initial: allocation,
							spillCost: unit Graph.node -> int,
							registers: Frame.register list} =
		let
			val nodeList = G.nodes(graph)
			val reg_number = List.length(registers)
			val simplifiedNode = getSimplifiedNode(nodeList, reg_number, moves, initial)

			val spills = []
		in
			case simplifiedNode of
				NONE => 
				(
					if (List.null(nodeList)) then (initial, [])
					else 
						let
							(* val _ = Liveness.show (TextIO.stdOut,interference); *)
						in
							
						(* (errorMsg "Cannot further simplify, should try coalesce and unfreeze."; (initial, [])) *)
						(initial, [])
						end
						
				)
			| SOME(curNode) => (* recursively continue simplification *)
				let
					val curNodeId = G.getNodeID(curNode)
					val graph' = G.removeNode(graph, curNodeId)
					val (curAlloc, _) = color({interference = Liveness.IGRAPH{graph = graph', tnode = tnode, gtemp = gtemp, moves = moves},
																	initial = initial,
																	spillCost = spillCost,
																	registers = registers})
					val neighNodes: G.nodeID list = G.adj(curNode)
					fun addNeighReg (curNeigh: G.nodeID, allocatedRegs) =
						case Tab.look(curAlloc, curNeigh) of
							NONE => allocatedRegs
						| SOME(neighReg) => S.add(allocatedRegs, neighReg)
					val neighRegs = foldl addNeighReg S.empty neighNodes
					val curReg = allocColor(curNode, registers, neighRegs)
				in
					case curReg of
						NONE => (errorMsg("Not enough register to allocate."); (curAlloc, []))
					| SOME(reg) => (Tab.enter(curAlloc, curNodeId, reg), [])
				end
			
		end

end
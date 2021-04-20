(*
data structures:
	1. control-flow graph(makegraph.sml):
		1) each node is with {def, use, ismove}, edge is directional
		2) iterate instructions and convert them into nodes, then connect by edges
	2. liveness map:
		1) <Temp.temp, {live-in, live-out}>
		2) iterate all nodes within control-flow graph, get liveness map by updating live-in and live-out until converging
	3. interferenceGraph:
		1) each node does not contain other information, edge is bidirectional
		2) heuristics: live-out cannot be allocated to the same register with dst register, so an edge should be connected between
*)

structure IGraph = Flow.Graph
structure Liveness: 
sig
	type data
	datatype igraph = 
		IGRAPH of {graph: unit IGraph.graph, 
					tnode: Temp.temp -> unit IGraph.node, (*a mapping from temporaries of the Ass program to graph nodes*)
					gtemp: unit IGraph.node -> Temp.temp, (*the inverse mapping, from graph nodes back to temporaries*)
					moves: (unit IGraph.node * unit IGraph.node) list} (*a list of move instructions*)

	val interferenceGraph:
		Flow.flowgraph -> 
			igraph * (data Flow.Graph.node -> Temp.temp list)

	val show : TextIO.outstream * igraph -> unit
end =

struct
	structure G = IGraph
	type temp = Temp.temp
	type data = temp
(*	type liveSet = unit Temp.Table.table * temp list 
	type liveMap = liveSet Flow.Graph.Table.table*)
	fun errorMsg msg = ErrorMsg.error 0 ("Compiler error: " ^ msg) 

	datatype igraph = 
		IGRAPH of {graph: unit IGraph.graph, 
					tnode: Temp.temp -> unit IGraph.node, (*a mapping from temporaries of the Ass program to graph nodes*)
					gtemp: unit IGraph.node -> Temp.temp, (*the inverse mapping, from graph nodes back to temporaries*)
					moves: (unit IGraph.node * unit IGraph.node) list} (*a list of move instructions*)

	structure M = RedBlackMapFn(
		struct
			type ord_key = int
			val compare = Int.compare
		end)
	structure S = RedBlackSetFn(
		struct
			type ord_key = temp
			val compare = Int.compare
		end)

	(* for each basic block, calculate its live-in and live-out *)
	type liveness_data = {live_in: S.set, live_out: S.set}

	(* used in liveness map iteration, to decide whether another iteration is needed *)
	fun isMapSame (map1: liveness_data M.map, map2: liveness_data M.map) =
    let
			fun getIsSame(nodeId: Temp.temp, {live_in = in1, live_out = out1}, prevIsSame) =
        case M.find(map2, nodeId) of
          NONE => false
        | SOME({live_in = in2, live_out = out2}) => prevIsSame andalso S.equal(in1, in2) andalso S.equal(out1, out2)
		in
			M.numItems(map1) = M.numItems(map2) andalso (M.foldli getIsSame true map1)
		end

	(* iterate through liveness map, update live-in and live-out until it keeps the same *)
	fun getLivenessMap (oldLivenessMap, nodeList) = (* nodeList: reversed nodes for instructions from control-flow graph *)
    let
			fun getUpdatedLiveInOut (curNode: Flow.info Flow.Graph.node, curLivenessMap) =
	    	let
					val {def, use, ismove} = G.nodeInfo(curNode)

					val updatedLiveOut =
						let
							fun addSuccLiveIn (succ: Temp.temp, curLiveOut) =
								case M.find(curLivenessMap, succ) of
								NONE => (errorMsg("successor does not exists in liveness map"); S.empty)
							| SOME({live_in, live_out}) => S.union(curLiveOut, live_in)
						in
							G.foldSuccs addSuccLiveIn S.empty curNode (* apply 'reduce' on successor nodes *)
						end

					val updatedLiveIn = S.union(S.fromList(use), S.difference(updatedLiveOut, S.fromList(def)))

          (* liveness map: <Temp.temp(aka int), {live-in, live-out}> *)
          val k: Temp.temp = G.getNodeID(curNode)
          val v = {live_in = updatedLiveIn, live_out = updatedLiveOut}
				in
					M.insert(curLivenessMap, k, v)
				end

				val newLivenessMap = foldl getUpdatedLiveInOut oldLivenessMap nodeList
		in
			if (isMapSame(oldLivenessMap, newLivenessMap)) then newLivenessMap
				else getLivenessMap(newLivenessMap, nodeList)
		end

	fun getInterferenceGraph (controlFlowGraph, livenessMap) =
		let
			(* add temporaries(variables) into interference graph *)
			fun addNodes (curNode: Flow.info G.node, curGraph) =
        let
          val {def, use, ismove} = G.nodeInfo(curNode)
          fun addNodeToGraph(temp: Temp.temp, g) = G.addNode(g, temp, ())
        in
          foldl addNodeToGraph curGraph (def@use)
        end

        val nodeList = G.nodes(controlFlowGraph)
        val g = foldl addNodes G.empty nodeList (* only nodes, no edges *)

      (* 
        1. iterate live-out temps, add edges between every live-out temp and dst
        2. live-out could get from foldli() liveness map
        3. dst could get from G.nodeInfo(node)
      *)
			fun addEgdes (nodeId: Temp.temp, {live_in, live_out}, curGraph) =
				let
          val curNode: Flow.info G.node = G.getNode(controlFlowGraph, nodeId)
					val {def, use, ismove} = G.nodeInfo(curNode)
					fun addEdgeToGraph(temp: Temp.temp, g) =
						if (List.null(def)) then g
						else foldl (fn (des, g) => G.doubleEdge(g, des, temp)) g def
				in
					S.foldl addEdgeToGraph curGraph live_out
				end

			val g' = M.foldli addEgdes g livenessMap (* iterate kv-pairs of livenessMap *)
		in
			g'
		end

  (*
    1. get "move" information from control-flow graph
    2. return list should contain nodes from interference graph
  *)
  fun getMoveList (nodeList, interferenceGraph) : (unit IGraph.node * unit IGraph.node) list =
    let
      fun getMoveListHelper (curNode: Flow.info Flow.Graph.node, curMoveList: (unit IGraph.node * unit IGraph.node) list) =
        let
          val {def, use, ismove} = G.nodeInfo(curNode)
        in
				(
					if (ismove andalso List.length(def) <> 1) then errorMsg("Move instruction should have one def.") else ();
					if (ismove andalso List.length(use) <> 1) then errorMsg("Move instruction should have one use.") else ();
          if (ismove) then
            let
              val reg1: Temp.temp = List.hd(def)
              val reg2: Temp.temp = List.hd(use)
              val node1: unit IGraph.node = G.getNode(interferenceGraph, reg1)
              val node2: unit IGraph.node = G.getNode(interferenceGraph, reg2)
            in
              curMoveList@[(node1, node2)]
            end
          else curMoveList
				)
        end
    in
      foldl getMoveListHelper [] nodeList
    end

	(*val show : outstream * igraph -> unit*)
	fun printIgraphNode (id, ()) = Temp.makestring id
	fun show (out, IGRAPH{graph,...}) = G.printGraph printIgraphNode graph
	fun printLivenessMap(map) = 
		let
			val kvpairs = M.listItemsi map
			fun printTemps [] = ""
				| printTemps (t::l) = Temp.makestring t ^ "," ^ (printTemps l)
			fun printSet s = "[" ^ printTemps(S.listItems s) ^ "]"
			fun printKvpair (t, {live_in, live_out}) = print ("(" ^ (Temp.makestring t) ^ ":" ^ (printSet live_out) ^ ")\n")
		in
			print "LivenessMap:\n";
			app printKvpair kvpairs
		end

	(*
		1. Create an empty liveness map for each node
		2. Iterate the graph, update live-in and live-out until converge.
    @param: control-flow graph
	*)
	fun interferenceGraph controlFlowGragh =
		let
			val nodeList = G.nodes(controlFlowGragh) (* node of instruction *)
			fun insertNodeToLivenessMap (node, map) = M.insert(map, G.getNodeID(node), {live_in = S.empty, live_out = S.empty}) (*Map<int, {S.set, S.set}>*)
			val initLivenessMap = foldl insertNodeToLivenessMap M.empty nodeList (* initial liveness graph, with all live-in and live-out set empty *)
			val livenessMap = getLivenessMap(initLivenessMap, List.rev(nodeList)) (* start from end of instructions, iterate till live-in and live-out converged to a fixed point *)
			val interferenceGraph = getInterferenceGraph(controlFlowGragh, livenessMap)
			val moveList = getMoveList (nodeList, interferenceGraph)
			val igraph = IGRAPH {graph = interferenceGraph, moves = moveList,
					tnode = fn t => G.getNode(interferenceGraph, t),
					gtemp = G.getNodeID}
			fun getLiveOut node = S.listItems(#live_out(M.lookup(livenessMap, G.getNodeID node)))
		in
			printLivenessMap livenessMap;
			show (TextIO.stdOut,igraph);
			(igraph, getLiveOut)
		end

end

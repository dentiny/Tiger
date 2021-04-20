(*signature REGALLOC = 
sig
	structure Frame: FRAME
	type allocation = Frame.register Temp.Table.table
	val alloc: Assem.instr list * Frame.frame -> Assem.instr list * allocation
end
*)

(*manages spilling and calls upon Color as a subroutine.*)
structure RegAlloc : REGALLOC= 
struct
	structure Frame = MipsFrame
	structure F = Frame
	structure Tab = Temp.Table
	structure G = Flow.Graph
	type allocation = F.register Tab.table

	(*: unit Graph.node -> int *)
	fun spillCostHelper(cfg, regNode) = 
		let
			val reg = G.getNodeID regNode
			val insnNodes = G.nodes cfg
			val data = map G.nodeInfo insnNodes
			fun eqReg e = (e = reg)
			fun useDefCount({def,use,ismove}, count) = 
				count + List.length(List.filter eqReg (def@use))
			val count = foldl useDefCount 0 data
		in
			count
		end

	fun alloc (insns, frame) = 
		let
			val (cfg, nodes) = MakeGraph.instrs2graph insns
      		val (igraph, getLiveOut) = Liveness.interferenceGraph cfg
      		val (regMap, tlist) = Color.color {
      			interference=igraph,
				initial=F.tempMap,
				spillCost= (fn reg => spillCostHelper(cfg, reg)),
				registers=F.registers}
		in
			(insns, regMap)
		end

end
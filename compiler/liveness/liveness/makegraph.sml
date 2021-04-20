structure MakeGraph:
sig 
  type info
  (*val instrs2graph: Assem.instr list -> Flow.flowgraph * Flow.Graph.node list *)
  val instrs2graph: Assem.instr list -> Flow.flowgraph * info Flow.Graph.node list
end = 

struct
  structure A = Assem
  structure G = Flow.Graph
  structure S = Symbol
  type info = Flow.info
  fun print_labels [] = ""
    | print_labels (a::l) = Temp.makestring a ^ "," ^ (print_labels l)
  fun print_node (id, {def, use, ismove}) = Int.toString id ^ 
    ": use=[" ^ (print_labels use) ^
    "], def=[" ^ (print_labels def) ^ "], ismove=" ^ 
    (Bool.toString ismove)


  fun instrs2graph insns =  
    let
      val g : info G.graph = G.empty
      val label2node : int S.table ref = ref S.empty

      (*generate all nodes. Not connnected yet. need a Map<label, node> *)
      fun gene_node(g, id, A.OPER{assem,dst,src,jump}) = 
            G.addNode(g, id, {def=dst, use=src, ismove=false})
        | gene_node(g, id, A.MOVE{assem,dst,src}) = 
            G.addNode(g, id, {def=[dst], use=[src], ismove=true})
        | gene_node(g, id, A.LABEL{assem,lab}) =
          let
            val (g, node) = G.addNode'(g, id, {def=[], use=[], ismove=false})
          in
            label2node := S.enter(!label2node, lab, id); g
          end
      fun gene_nodes(g, [], i) = g
        | gene_nodes(g, insn::l, i) = gene_nodes(gene_node(g,i,insn), l, i+1)
      val g' = gene_nodes(g, insns, 1)

      (*add edges*)
      val len = List.length insns
      fun add_edges(g, [], i) = g
        | add_edges(g, A.OPER{assem,dst,src,jump=SOME(labels)}::l, i) =
            let
              fun addLabelSucc(label, g) = G.addEdge(g, {from=i, to=valOf(S.look(!label2node,label))})
              val g' = foldl addLabelSucc g labels
            in
              add_edges(g', l, i+1)
            end
        | add_edges(g, c::n::l, i) = add_edges(G.addEdge(g, {from=i, to=i+1}), n::l, i+1)
        | add_edges(g, [c], i) = g
      val g'' = add_edges(g', insns, 1)
        
    in
      G.printGraph print_node g'';
      (g'', G.nodes g'')
    end
end

structure Main = struct

  structure Tr = Translate
  structure F = MipsFrame
  structure R = RegAlloc
  structure Tab = Temp.Table

  fun getMaxArgNumber (F.STRING(lab,s), maxArgNumber) = maxArgNumber
    | getMaxArgNumber (F.PROC{body,frame}, maxArgNumber) = Int.max(maxArgNumber, List.length (F.formals frame))

  fun getsome (SOME x) = x
  val dataStarted = ref false 
  fun emitproc out (F.PROC{body,frame}) =
    let 
      val _ = print ("emit " ^ S.name (F.name frame) ^ "\n")
      (*munchStm(T.LABEL(Frame.name frame));*)
       (* val _ = Printtree.printtree(out,body); *)
      val stms = Canon.linearize body
        (*val _ = app (fn s => Printtree.printtree(out,s)) stms;  *)
      val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
      val instrs =  List.concat(map (MipsGen.codegen frame) stms') 
      val instrs' = F.procEntryExit2(frame, instrs)
      val (instrs'', regMap) = R.alloc(instrs', frame)
      (* val instrs' = instrs *)
      val argNum = foldl getMaxArgNumber 0 (Tr.getResult())
      val {prolog, body, epilog} = (F.procEntryExit3(frame, instrs'', argNum))
      val _ = TextIO.output(out,prolog)
      (*val format0 = Assem.format(Temp.makestring)*)
      val format0 = Assem.format(fn reg => case Tab.look(regMap, reg) of SOME reg => reg | NONE => Temp.makestring reg)
    in  app (fn i => TextIO.output(out,format0 i)) body;
        TextIO.output(out,epilog)
    end
  | emitproc out (F.STRING(lab,s)) = 
    if !dataStarted then TextIO.output(out,F.string(lab,s)) 
    else (dataStarted := true; TextIO.output(out,(".data\n" ^ F.string(lab,s))))
  

  fun withOpenFile fname f = 
    let
      val out = TextIO.openOut(fname)
    in
      (f out before TextIO.closeOut out) 
      handle e => (TextIO.closeOut out; raise e)
    end 

  fun compile filename = 
    let
      val absyn = Parse.parse filename
      val frags = (FindEscape.findEscape absyn; Semant.transProg absyn)
      val outfile = List.last(String.tokens (fn c => c = #"/") filename) ^ ".s" (* ../../testcases/test1.tig -> test1.tig.s *)
    in 
        withOpenFile outfile
          (fn out => (app (emitproc out) frags))
    end

end




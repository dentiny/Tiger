structure MipsFrame : FRAME =
struct
  type register = string

  (* Formals and locals may be in the frame or in registers. *)
  datatype access = InFrame of int (* InFrame(X) indicates a memory location at offset X from the frame pointer *)
		              | InReg of Temp.temp (* InReg(t64) indicates that it will be held in register t64 *)

  (*The type frame holds information about formal parameters and 
  	local variables allocated in this frame.*)
  type frame = {name: Temp.label, formals: access list, locals: int ref}
  
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  (* Registers *)
  val wordSize = 4
  val ZERO = Temp.newtemp()
  val AT = Temp.newtemp()
  val V0 = Temp.newtemp()
  val V1 = Temp.newtemp()
  val A0 = Temp.newtemp()
  val A1 = Temp.newtemp()
  val A2 = Temp.newtemp()
  val A3 = Temp.newtemp()
  val T0 = Temp.newtemp()
  val T1 = Temp.newtemp()
  val T2 = Temp.newtemp()
  val T3 = Temp.newtemp()
  val T4 = Temp.newtemp()
  val T5 = Temp.newtemp()
  val T6 = Temp.newtemp()
  val T7 = Temp.newtemp()
  val T8 = Temp.newtemp()
  val T9 = Temp.newtemp()
  val S0 = Temp.newtemp()
  val S1 = Temp.newtemp()
  val S2 = Temp.newtemp()
  val S3 = Temp.newtemp()
  val S4 = Temp.newtemp()
  val S5 = Temp.newtemp()
  val S6 = Temp.newtemp()
  val S7 = Temp.newtemp()
  val K0 = Temp.newtemp()
  val K1 = Temp.newtemp()
  val GP = Temp.newtemp()
  val SP = Temp.newtemp()
  val FP = Temp.newtemp()
  val RA = Temp.newtemp()

  val specialregs = [ZERO, AT, V0, V1, K0, K1, GP, SP, FP, RA]
  val argregs = [A0, A1, A2, A3]
  val calleesaves = [S0, S1, S2, S3, S4, S5, S6, S7]
  val callersaves = [T0, T1, T2, T3, T4, T5, T6, T7, T8, T9]


  val specialregs_list = [(ZERO, "$r0"), (AT, "$at"), (V0, "$v0"), (V1, "$v1"), (K0, "$k0"), (K1, "$k1"), (GP, "$gp"), (SP, "$sp"), (FP, "$fp"), (RA, "$ra")]
  val argregs_list = [(A0, "$a0"), (A1, "$a1"), (A2, "$a2"), (A3, "$a3")]
  val calleesaves_list = [(S0, "$s0"), (S1, "$s1"), (S2, "$s2"), (S3, "$s3"), (S4, "$s4"), (S5, "$s5"), (S6, "$s6"), (S7, "$s7")]
  val callersaves_list = [(T0, "$t0"), (T1, "$t1"), (T2, "$t2"), (T3, "$t3"), (T4, "$t4"), (T5, "$t5"), (T6, "$t6"), (T7, "$t7"), (T8, "$t8"), (T9, "$t9")]
  val tempMap =
    let
      fun addToMap ((reg, name), curMap) = Temp.Table.enter(curMap, reg, name)
	  in
		  foldl addToMap Temp.Table.empty (specialregs_list @ argregs_list @ calleesaves_list @ callersaves_list)
	  end

  fun string (lab,s) = S.name lab ^ ":\t.word " ^ Int.toString(String.size s) ^ "\n.asciiz \"" ^ s ^ "\"\n"
  (* display assembly prior to register allocation *)
  fun getRegister (reg: Temp.temp) : string =
    case Temp.Table.look(tempMap, reg) of
      SOME(s) => s
		| NONE => Temp.makestring(reg)

  val registers = map getRegister (calleesaves@callersaves@argregs@specialregs)

  fun exp (InReg(k))(_) = Tree.TEMP(k)
    | exp (InFrame(k))(fp) = Tree.MEM(Tree.BINOP(Tree.PLUS, fp, Tree.CONST(k)))

  fun newFrame {name = f, formals = l} =
  	let
  		val locals = ref 0
  		(*escape true: inner function may use the variable. Put it in the frame.*)
  		(*otherwise put it in a register*)
  		fun allocFormal true = (locals := (!locals) + 1; InFrame (!locals * ~wordSize))
  			| allocFormal false = InReg(Temp.newtemp())
  	in
  		{name = f, formals = map allocFormal l, locals = locals} (*TODO: init value of local*)
  	end

  fun allocLocal {name, formals, locals} true = (locals := !locals + 1; InFrame (!locals * ~wordSize))
  	| allocLocal {name, formals, locals} false = InReg(Temp.newtemp())

  fun name 	  {name, formals, locals} = name
  fun formals {name, formals, locals} = formals
  
  fun externalCall(func, args) = Tree.CALL(Tree.NAME(Temp.namedlabel(func)), args)

  fun seq [] = (Tree.EXP(Tree.CONST(0)))
    | seq [s] = s
    | seq [s1, s2] = Tree.SEQ(s1, s2)
    | seq (a::l) = Tree.SEQ(a, seq(l))

  (*
    view shift:
    1. caller moves arguments into register and frame if spills
    2. callee moves arguments from argument registers(A0-A3) and frame to registers allocated
  *)
  fun procEntryExit1(frame, body: Tree.stm) : Tree.stm =
    let
      val accesses: access list = formals(frame)
      val argCount = List.length(accesses)
      fun getViewShift (index) =
        if (index = argCount) then []
        else
          let
            val curFormal: access = List.nth(accesses, index)
            val src = if (index < 4) then Tree.TEMP(List.nth(argregs, index))
                      else Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP(FP), Tree.CONST(wordSize * (index - 4))))
            val dst = exp(curFormal)(Tree.TEMP(FP))
            val moveIns = Tree.MOVE(dst, src)
          in
            moveIns :: getViewShift(index + 1)
          end
      val viewShiftIns = getViewShift(0)
    in
      seq(viewShiftIns @ [body])
    end

  fun procEntryExit2 (frame, body) =
    body@[Assem.OPER{assem = "",
						        (*src = [ZERO, RA, SP]@calleesaves,*)
                    src = specialregs,
                    (*src = [ZERO, RA, SP],*)
						        dst = [],
						        jump = SOME([])}]

  (* 
    sw $fp, -fpOffset($sp)
    move $fp, $sp
    addi $sp, $fp, -offset
    store RA, callee-saves

    restore RA, callee-saves
    move $sp, $fp
    lw $fp, -fpOffset($fp)
  *)
  (*
    frame arrangement:
      local variable <- indicated by !locals
      FP
      callee-saves <- currently all of them
      RA
      arguments to make function call
  *)
  fun procEntryExit3 ({name, formals, locals}, body, argsNum) = (*TODO: argsNum*)
    let
      fun int (v: int) : string = if (v >= 0) then Int.toString(v) else "-" ^ Int.toString(~v)
      val labelIns = Assem.LABEL{assem = Symbol.name(name) ^ ":\n", lab = name}

      (* runtime.c doesn't pass FP as the first argument, for tig_main manually fix it *)
      val fpFix = Assem.OPER{assem = "move `d0, `s0\n",
				                      src=[FP], 
                              dst=[A0], 
                              jump = NONE}

      fun moveInsn(dst,src) = Assem.MOVE{assem = "move `d0, `s0\n", src = src, dst = dst}
      fun spUpdateIns bytes= Assem.OPER{assem = "addi `d0, `s0, " ^ int(bytes) ^ "\n",
                                    src = [SP],
                                    dst = [SP],
                                    jump = NONE}
      val savedRegs = calleesaves@[RA]
      val offset = !locals + 1 + List.length(savedRegs) + argsNum

      val fpOffset = (!locals + 1) * ~wordSize
      val storeFP = Assem.OPER{assem = "sw `s0, " ^ int(fpOffset) ^ "(`s1)\n", src = [FP, SP], dst = [], jump = NONE}
      val loadFP  = Assem.OPER{assem = "lw `d0, " ^ int(fpOffset) ^ "(`s0)\n", src = [FP], dst = [FP], jump = NONE}
      fun getStoreIns index =
        if (index >= List.length(savedRegs)) then []
        else
          let
            val curOffset = ((!locals + 2) + index) * ~wordSize
            val curReg = List.nth(savedRegs, index)
            val curCalleeRegIns = Assem.OPER{assem = "sw `s0, " ^ int(curOffset) ^ "(`s1)\n",
                                              src = [curReg, FP],
                                              dst = [],
                                              jump = NONE}
          in
            curCalleeRegIns :: getStoreIns(index + 1)
          
          end
      val calleeSavesStoreIns = getStoreIns(0)

      fun getRestoreIns index =
        if (index >= List.length(savedRegs)) then []
        else
          let
            val curOffset = ((!locals + 2) + index) * ~wordSize
            val curReg = List.nth(savedRegs, index)
            val curCalleeRegIns = Assem.OPER{assem = "lw `d0, " ^ int(curOffset) ^ "(`s0)\n",
                                              src = [FP],
                                              dst = [curReg],
                                              jump = NONE}
          in
            curCalleeRegIns :: getRestoreIns(index + 1)
          end
      val calleeSavesRestoreIns = getRestoreIns(0)
      val returnIns = Assem.OPER{assem = "jr `d0\n",
				                          src = [],
                                  dst = [RA],
                                  jump = NONE}

    in
      {prolog = "",
        body = [labelIns]
                @ (if Symbol.name(name) = "tig_main" then [fpFix] else [])
                @ [storeFP]
                @ [moveInsn(FP,SP)] 
                @ [spUpdateIns(~wordSize * offset)] (*TODO*)
                @ calleeSavesStoreIns 
                @ body 
                @ calleeSavesRestoreIns
                @ [moveInsn(SP, FP)]
                @ [loadFP]
                (*@ [spUpdateIns(wordSize * offset)] *)
                @ [returnIns],
        epilog = ""}

    end
    
end
structure MipsGen : CODEGEN =
struct

structure Frame = MipsFrame
structure A = Assem
structure T = Tree
structure S = Symbol

fun bugErr str = ErrorMsg.error 0 ("[Compiler error]" ^ str)

fun codegen (frame) (stm: Tree.stm) : Assem.instr list =
  let
    val ilist = ref (nil: A.instr list)
    fun emit x = ilist := x :: !ilist
    fun result (gen) = let val t = Temp.newtemp() in gen t; t end

    fun int (v: int) : string = if (v >= 0) then Int.toString(v) else "-" ^ Int.toString(~v)

    fun cvtRelop (T.EQ) = "beq"
      | cvtRelop (T.NE) = "bne"
      | cvtRelop (T.LT) = "blt"
      | cvtRelop (T.LE) = "ble"
      | cvtRelop (T.GT) = "bgt"
      | cvtRelop (T.GE) = "bge"
      | cvtRelop (_) = (bugErr "cvtRelop meets unexpected relop."; "")

    fun cvtBinop (T.PLUS) = "add"
      | cvtBinop (T.MINUS) = "sub"
      | cvtBinop (T.MUL) = "mul"
      | cvtBinop (T.DIV) = "div"
      | cvtBinop (_) = (bugErr "cvtBinop meets unexpected binop."; "")

    fun munchStm(T.SEQ(a,b)) = (munchStm a; munchStm b)
      
      (* jump *)
      | munchStm(T.JUMP(T.NAME(label), labels)) =
          emit(A.OPER{assem="j " ^ S.name(label) ^ "\n", (* eg: j label *)
            src=[],
            dst=[],
            jump=SOME(labels)})
      | munchStm(T.CJUMP(relop, exp1, exp2, label1, label2)) =
          emit(A.OPER{assem=cvtRelop(relop) ^ " `s0, `s1, " ^ S.name(label1) ^ "\n", (* eg: beq $1, $2, label *)
                src=[munchExp(exp1), munchExp(exp2)],
                dst=[],
                jump=SOME([label1, label2])})

      (* sw *)
      | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i)),e2)) =
          emit(A.OPER{assem="sw `s1, " ^ int i ^ "(`s0)\n",
            src=[munchExp e1, munchExp e2],
            dst=[],
            jump=NONE})
      | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS,T.CONST i,e1)),e2)) =
          emit(A.OPER{assem="sw `s1, " ^ int i ^ "(`s0)\n",
            src=[munchExp e1, munchExp e2],
            dst=[],
            jump=NONE})
      | munchStm(T.MOVE(T.MEM(T.CONST i),e2)) =
          emit(A.OPER{assem="sw `s0, " ^ int i ^ "(r0)\n",
            src=[munchExp e2],
            dst=[],
            jump=NONE})
      | munchStm(T.MOVE(T.MEM(e1),e2)) =
          emit(A.OPER{assem="sw `s1, 0(`s0)\n",
            src=[munchExp e1, munchExp e2],
            dst=[],
            jump=NONE})
      | munchStm(T.MOVE(T.TEMP t, T.CONST i) ) =
          emit(A.OPER{assem="li `d0, " ^ int i ^ "\n",
            src=[],
            dst=[t],
            jump=NONE})
      | munchStm(T.MOVE(T.TEMP t, e2) ) =
          emit(A.MOVE{assem="move `d0, `s0\n",
            src=munchExp e2,
            dst=t})

      | munchStm(T.LABEL lab) =
          emit(A.LABEL{assem=S.name lab ^ ":\n", lab=lab})
      | munchStm(T.EXP(exp)) = (munchExp(exp); ())
      | munchStm(_) = (bugErr "munchStm meets unexpected statement"; ())

    and

        (* lw *)
        munchExp(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i))) =
          result(fn r => emit(A.OPER{assem="lw `d0, " ^ int i ^ "(`s0)\n",
            src=[munchExp e1],
            dst=[r],
            jump=NONE}))
      | munchExp(T.MEM(T.BINOP(T.PLUS,T.CONST i,e1))) =
          result(fn r => emit(A.OPER{assem="lw `d0, " ^ int i ^ "(`s0)\n",
            src=[munchExp e1],
            dst=[r],
            jump=NONE}))
      | munchExp(T.MEM(T.CONST i)) =
          result(fn r => emit(A.OPER{assem="lw `d0, " ^ int i ^ "(r0)\n",
            src=[],
            dst=[r],
            jump=NONE}))
      | munchExp(T.MEM(e1)) =
          result(fn r => emit(A.OPER{assem="lw `d0, 0(`s0)\n",
            src=[munchExp e1],
            dst=[r],
            jump=NONE}))

      (* binop *)
      | munchExp(T.BINOP(oper, T.CONST(_), T.CONST(_))) = (bugErr "constant folding should already been completed in IR."; Temp.newtemp())
      | munchExp(T.BINOP(T.PLUS,e1,T.CONST i)) =
          result(fn r => emit(A.OPER{assem="addi `d0, `s0," ^ int i ^ "\n",
            src=[munchExp e1],
            dst=[r],
            jump=NONE}))
      | munchExp(T.BINOP(T.PLUS,T.CONST i,e1)) =
          result(fn r => emit(A.OPER{assem="addi `d0, `s0," ^ int i ^ "\n",
            src=[munchExp e1],
            dst=[r],
            jump=NONE}))
      | munchExp(T.BINOP(oper,e1,e2)) =
          result(fn r => emit(A.OPER{assem=cvtBinop(oper) ^ " `d0, `s0, `s1\n",
            src=[munchExp e1, munchExp e2],
            dst=[r],
            jump=NONE}))
      
      | munchExp(T.ESEQ(stm, exp)) = (munchStm(stm); munchExp(exp))
      | munchExp(T.NAME(label)) = 
          result(fn r => emit(A.OPER{assem="la `d0, " ^ S.name label ^ "\n",
            src=[],
            dst=[r],
            jump=NONE}))
      | munchExp(T.CONST i) =
          result(fn r => emit(A.OPER{assem="li `d0, " ^ int i ^ "\n",
            src=[],
            dst=[r],
            jump=NONE}))
      | munchExp(T.TEMP t) = t
      | munchExp(T.CALL(T.NAME(name), args)) =
        let
          val arg_count = List.length(args)
          val offset =
            if (arg_count <= 4) then ~Frame.wordSize
            else (arg_count - 4 + 1) * (~Frame.wordSize)
          (* val sp_addr1 = T.BINOP(T.PLUS, T.TEMP(Frame.SP), T.CONST(offset)) (* call prolog: SP = SP + offset *)
          val sp_addr2 = T.BINOP(T.PLUS, T.TEMP(Frame.SP), T.CONST(~offset)) (* call epilog: SP = SP - offset *)
          val fp_addr1 = T.BINOP(T.PLUS, T.TEMP(Frame.FP), T.CONST(offset)) (* call prolog: FP = FP + offset *)
          val fp_addr2 = T.BINOP(T.PLUS, T.TEMP(Frame.FP), T.CONST(~offset)) (* call epilog: FP = FP - offset *)
          val static_link_addr = T.BINOP(T.PLUS, T.TEMP(Frame.SP), T.CONST(Frame.wordSize))
          val updateSP1 = T.MOVE(T.TEMP(Frame.SP), sp_addr1) (* call prolog *)
          val updateSP2 = T.MOVE(T.TEMP(Frame.SP), sp_addr2) (* call epilog *)
          val updateFP1 = T.MOVE(T.TEMP(Frame.FP), fp_addr1) (* call prolog *)
          val updateFP2 = T.MOVE(T.TEMP(Frame.FP), fp_addr2) (* call epilog *)
          val placeStaticLink = T.MOVE(T.MEM(static_link_addr), T.TEMP(Frame.FP)) *)
          val prolog =  "#procedure call begins\n" ^
                        "addi $sp, $sp, " ^ int(offset) ^ "\n" ^
                        "sw $fp, 4($sp)\n" ^
                        "addi $fp, $fp, " ^ int(offset) ^ "\n";
(*          val epilog =  "addi $sp, $sp, " ^ int(~offset) ^ "\n" ^
                        "addi $fp, $fp, " ^ int(~offset) ^ "\n" ^
                        "jr $ra\n" ^
                        "#procedure call ends\n"*)
(*          val epilog = "jr $ra\n" ^ 
                "#procedure call ends\n";*)
        in
        (
          (* emit(A.OPER{assem=prolog,
                src=[],
                dst=[],
                jump=NONE}); *)
          emit(A.OPER{assem="jal " ^ S.name(name) ^ "\n",
            src=munchArgs(0, args), (* list of temps are to be passed to jal *)
            dst=Frame.callersaves@Frame.argregs@[Frame.V0, Frame.V1, Frame.RA],
            jump=NONE});
(*           emit(A.OPER{assem=epilog,
                src=[],
                dst=[],
                jump=NONE});*) 
          Frame.V0
        )
        end
      | munchExp(_) = (bugErr "munchExp meets unexpected expression"; Temp.newtemp())

    and
      
      munchArgs(index, args) =
        if (index >= List.length(args)) then []
        else if (index < 4) then (* place at register *)
          let
            val arg = List.nth(args, index)
            val reg = List.nth(Frame.argregs, index)
            val stm = T.MOVE(T.TEMP(reg), arg)
          in
            munchStm(stm);
            [munchExp(T.TEMP(reg))]@munchArgs(index + 1, args)
          end
        else (* place at frame *)
          let
            val arg = List.nth(args, index)
            val offset = T.CONST((index + 1 - 4) * Frame.wordSize) (* address from SP to FP: static, arg1, arg2 *)
            val addr = T.BINOP(T.PLUS, T.TEMP(Frame.SP), offset)
            val stm = T.MOVE(T.MEM(addr), arg)
          in
            munchStm(stm);
            munchArgs(index + 1, args)
          end

  in
    munchStm stm;
    rev(!ilist)
  end

end
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

  fun string (lab,s) = S.name lab ^ ":\t.asciiz \"" ^ s ^ "\"\n"
  (* display assembly prior to register allocation *)
  fun getRegister (reg: Temp.temp) : string =
    case Temp.Table.look(tempMap, reg) of
      SOME(s) => s
		| NONE => Temp.makestring(reg)

  fun exp (InReg(k))(_) = Tree.TEMP(k)
    | exp (InFrame(k))(fp) = Tree.MEM(Tree.BINOP(Tree.PLUS, fp, Tree.CONST(k)))

  fun newFrame {name = f, formals = l} =
  	let
  		val formalOffset = ref 0
  		(*escape true: inner function may use the variable. Put it in the frame.*)
  		(*otherwise put it in a register*)
  		fun allocFormal true = (formalOffset := (!formalOffset) + wordSize; InFrame (!formalOffset))
  			| allocFormal false = InReg(Temp.newtemp())
  	in
  		{name = f, formals = map allocFormal l, locals = ref ~1}
  	end

  fun allocLocal {name, formals, locals} true = (locals := !locals + 1; InFrame (!locals * ~wordSize))
  	| allocLocal {name, formals, locals} false = InReg(Temp.newtemp())

  fun name 	  {name, formals, locals} = name
  fun formals {name, formals, locals} = formals
  
  fun externalCall(func, args) = Tree.CALL(Tree.NAME(Temp.namedlabel(func)), args)

  fun procEntryExit1(frame,body) = body

  fun procEntryExit2 (frame, body) =
    body@[Assem.OPER{assem = "",
						        src = [ZERO, RA, SP]@calleesaves,
						        dst = [],
						        jump = SOME([])}]

  fun procEntryExit3 ({name, formals, locals}, body) =
    (*{prolog = "PROCEDURE " ^ Symbol.name(name) ^ "\n",*)
    {prolog = Symbol.name(name) ^ ":\n",
      body = body,
      (*epilog = "END " ^ Symbol.name(name) ^ "\n"}*)
      epilog = "jr $ra\n"}

end
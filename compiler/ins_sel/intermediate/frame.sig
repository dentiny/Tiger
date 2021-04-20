signature FRAME =
sig
  type access
  type frame
  type register
  datatype frag = PROC of {body: Tree.stm, frame: frame}
              | STRING of Temp.label * string
  val ZERO : Temp.temp
  val AT : Temp.temp
  val V0 : Temp.temp
  val V1 : Temp.temp
  val A0 : Temp.temp
  val A1 : Temp.temp
  val A2 : Temp.temp
  val A3 : Temp.temp
  val T0 : Temp.temp
  val T1 : Temp.temp
  val T2 : Temp.temp
  val T3 : Temp.temp
  val T4 : Temp.temp
  val T5 : Temp.temp
  val T6 : Temp.temp
  val T7 : Temp.temp
  val T8 : Temp.temp
  val T9 : Temp.temp
  val S0 : Temp.temp
  val S1 : Temp.temp
  val S2 : Temp.temp
  val S3 : Temp.temp
  val S4 : Temp.temp
  val S5 : Temp.temp
  val S6 : Temp.temp
  val S7 : Temp.temp
  val K0 : Temp.temp
  val K1 : Temp.temp
  val GP : Temp.temp
  val SP : Temp.temp
  val FP : Temp.temp
  val RA : Temp.temp
  val string : Temp.label * string -> string
  val specialregs : Temp.temp list
  val argregs : Temp.temp list
  val calleesaves : Temp.temp list
  val callersaves : Temp.temp list
  val wordSize : int
  val exp : access -> Tree.exp -> Tree.exp
  val newFrame : {name: Temp.label, formals: bool list} -> frame
  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access
  val externalCall : string * Tree.exp list -> Tree.exp
  val tempMap : register Temp.Table.table
  val getRegister : Temp.temp -> string (* display assembly prior to register allocation *)
  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
  val procEntryExit3 : frame * Assem.instr list -> {prolog: string, body : Assem.instr list, epilog: string}

end
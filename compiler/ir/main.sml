structure Main =
struct
  fun main filename =
    let
      val AST = Parse.parse filename
      val fragList = Semant.transProg(AST)
      fun printIR(MipsFrame.STRING(l, s)) = print("string literal: " ^ s ^ " with label: " ^ Symbol.name(l) ^ "\n")
        | printIR(MipsFrame.PROC{body, ...}) = Printtree.printtree(TextIO.stdOut, body)
    in
       app printIR fragList
    end
end
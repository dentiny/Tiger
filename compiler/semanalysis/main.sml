structure Main =
struct
  fun main filename =
    let
      val AST = Parse.parse filename
    in
      Semant.transProg AST
    end
end
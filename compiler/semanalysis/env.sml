structure Env : ENV =
struct

  type access = unit (*placeholder*)
  type ty = Types.ty

  datatype enventry = 
      VarEntry of {ty: ty}
    | FunEntry of {formals: ty list, result: ty}

  (* util to initialize base_tenv and base_venv *)
  fun addEntry((curSym, curType), curMap) = Symbol.enter(curMap, curSym,curType)

  (* initial type environment with built-in types *)
  val base_tenv = 
    let
      val builtinTypes = [(Symbol.symbol("string"), Types.STRING), 
                          (Symbol.symbol("int"), Types.INT)]
    in
      foldl addEntry Symbol.empty builtinTypes
    end

  (* initial variable environment with built-in function *)
  val base_venv =
    let 
      val builtinFunctions = [(Symbol.symbol("print"), FunEntry{formals = [Types.STRING], result = Types.UNIT}),
                              (Symbol.symbol("flush"), FunEntry{formals = [], result = Types.UNIT}),
                              (Symbol.symbol("getchar"), FunEntry{formals = [], result = Types.STRING}),
                              (Symbol.symbol("ord"), FunEntry{formals = [Types.STRING], result = Types.INT}),
                              (Symbol.symbol("chr"), FunEntry{formals = [Types.INT], result = Types.STRING}),
                              (Symbol.symbol("size"), FunEntry{formals = [Types.STRING], result = Types.INT}),
                              (Symbol.symbol("substring"), FunEntry{formals = [Types.STRING, Types.INT, Types.INT], result = Types.STRING}),
                              (Symbol.symbol("concat"), FunEntry{formals = [Types.STRING, Types.STRING], result = Types.STRING}),
                              (Symbol.symbol("not"), FunEntry{formals = [Types.INT], result = Types.INT}),
                              (Symbol.symbol("exit"), FunEntry{formals = [Types.INT], result = Types.UNIT})
                            ]
    in
      foldl addEntry Symbol.empty builtinFunctions
    end

end
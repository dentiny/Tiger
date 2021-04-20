structure Env : ENV =
struct

  type access = unit (*placeholder*)
  type ty = Types.ty

  datatype enventry =
      VarEntry of {access: Translate.access, ty: ty}
		| FunEntry of {level: Translate.level, label: Temp.label, formals: ty list, result: ty}

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
      fun getFunEntry(formals, result) = FunEntry{level = Translate.outermost, label = Temp.newlabel(), formals = formals, result = result}
      val builtinFunctions = [(Symbol.symbol("print"), getFunEntry([Types.STRING], Types.UNIT)),
                              (Symbol.symbol("flush"), getFunEntry([], Types.UNIT)),
                              (Symbol.symbol("getchar"), getFunEntry([], Types.STRING)),
                              (Symbol.symbol("ord"), getFunEntry([Types.STRING], Types.INT)),
                              (Symbol.symbol("chr"), getFunEntry([Types.INT], Types.STRING)),
                              (Symbol.symbol("size"), getFunEntry([Types.STRING], Types.INT)),
                              (Symbol.symbol("substring"), getFunEntry([Types.STRING, Types.INT, Types.INT], Types.STRING)),
                              (Symbol.symbol("concat"), getFunEntry([Types.STRING, Types.STRING], Types.STRING)),
                              (Symbol.symbol("not"), getFunEntry([Types.INT], Types.INT)),
                              (Symbol.symbol("exit"), getFunEntry([Types.INT], Types.UNIT))
                            ]
    in
      foldl addEntry Symbol.empty builtinFunctions
    end

end

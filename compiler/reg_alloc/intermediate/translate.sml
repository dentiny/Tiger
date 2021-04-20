structure Translate : TRANSLATE =
struct

structure Frame : FRAME = MipsFrame

structure A = Absyn
structure T = Tree
structure F = Frame
structure S = Symbol

(*
  LabelStringMap maps label to string literal, used for string literal comparison at compile-time
  key: Symbol.name(Temp.label)
    Every single unique string is generated a unique label, promised by strLiteralMap and transStr
  value: string literal itself
*)
structure StringKey =
  struct
    type ord_key = string
    val compare = String.compare
  end
structure LabelStringMap = RedBlackMapFn(StringKey)
val labelStringMap: string LabelStringMap.map ref = ref LabelStringMap.empty (* <symbol name of label(string), string literal> *)

type frag = F.frag
val fragList: frag list ref = ref []
val error = ErrorMsg.error 0
fun bugErr str = error ("[Compiler error]" ^ str)

(* Two types of representation of expression in IR Tree: T.exp and T.stm. *)
datatype exp =
  Ex of T.exp
| Nx of T.stm
| Cx of Temp.label * Temp.label -> T.stm

datatype level =
  BaseLevel
| Level of {parent: level, frame: F.frame, levelRef: unit ref}

val outermost = BaseLevel

type access = level * Frame.access

(*
  unEx, unNx, unCx converts Tree.exp into another form.
  unNx is called everywhere a non-return statement is needed, eg: body of while and for, etc.
  unCx is called everywhere a cond is used, eg: if, for, while, etc.
*)

(* Tree.stm list -> Tree.stm *)
fun seq [] = (T.EXP(T.CONST(0)))
  | seq [s] = s
  | seq [s1, s2] = T.SEQ(s1, s2)
  | seq (a::l) = T.SEQ(a, seq(l))

(* exp -> Tree.exp *)
fun unEx (Ex e) = e
  | unEx (Nx s) = T.ESEQ(s, T.CONST(0))
  | unEx (Cx bf) =
    let
      val res = Temp.newtemp() (* register for result *)
	    val t = Temp.newlabel() (* true label *)
      val f = Temp.newlabel() (* false label *)
    in
      T.ESEQ(seq[T.MOVE(T.TEMP(res), T.CONST(1)),
        bf(t, f),
        T.LABEL(f),
        T.MOVE(T.TEMP(res), T.CONST(0)),
        T.LABEL(t)],
	      T.TEMP(res))
    end

(* exp -> Tree.stm *)
fun unNx (Nx s) = s
  | unNx (Ex e) = T.EXP(e)
  | unNx (Cx bf) =
    let
      val lab = Temp.newlabel()
    in
      (bf(lab, lab); T.LABEL(lab))
    end

(* exp -> (Temp.label * Temp.label -> T.stm) *)
fun unCx (Cx bf) = bf
  | unCx (Nx s) = (bugErr "convert Translate.exp to Cx"; fn (l1,l2) => seq[]) 
  | unCx (Ex(T.CONST(0))) = (fn (t, f) => T.JUMP(T.NAME(f), [f]))
  | unCx (Ex(T.CONST(_))) = (fn (t, f) => T.JUMP(T.NAME(t), [t]))
  | unCx (Ex e) = fn (t, f) => T.CJUMP(T.NE, e, T.CONST(0), t, f)

(* utils for constant folding *)
fun isConstant(Ex(T.CONST(_))) = true
  | isConstant(Ex(T.ESEQ(T.EXP(T.CONST(0)), T.CONST(_)))) = true
  | isConstant(_) = false

fun isConstantValFalse(Ex(T.CONST(0))) = true
  | isConstantValFalse(Ex(T.ESEQ(T.EXP(T.CONST(0)), T.CONST(0)))) = true
  | isConstantValFalse(_) = false

fun isConstantValTrue(Ex(T.CONST(0))) = false
  | isConstantValTrue(Ex(T.CONST(_))) = true
  | isConstantValTrue(Ex(T.ESEQ(T.EXP(T.CONST(0)), T.CONST(0)))) = false
  | isConstantValTrue(Ex(T.ESEQ(T.EXP(T.CONST(0)), T.CONST(_)))) = true
  | isConstantValTrue(_) = false

fun getConstVal(Ex(T.CONST(v))) = v
  | getConstVal(Ex(T.ESEQ(T.EXP(T.CONST(0)), T.CONST(v)))) = v
  | getConstVal(_) = (bugErr "Cannot get arith value from a non-constant exp"; 0)

fun isStringLiteral (Ex(T.NAME(_))) = true
  | isStringLiteral (_) = false

fun getStringLiteral lab =
  case LabelStringMap.find(!labelStringMap, S.name(lab)) of
    NONE => (bugErr "Cannot get string literal value from a non-constant exp"; "")
  | SOME(v) => v

(* static link pre-pended at formals *)
fun newLevel {parent, name, formals} = Level {parent = parent, frame = F.newFrame{name=name, formals=true::formals}, levelRef = ref ()}

fun formals BaseLevel = (bugErr "BaseLevel does not contain frame" ;[])
  | formals (curLevel as Level{parent, frame, levelRef}) = 
        map (fn acc => (curLevel, acc)) (F.formals(frame))

(*val allocLocal : level -> bool -> access*)
fun allocLocal BaseLevel escape = (bugErr "alloc local on BaseLevel"; (BaseLevel, F.allocLocal (F.newFrame{name=Temp.newlabel(),formals=[]}) escape))
  | allocLocal (level as Level{parent, frame, levelRef}) escape = (level, F.allocLocal frame escape)

(* functions with same name would appear legally as test48. *)
structure M = RedBlackMapFn(
  struct
    type ord_key = string
    val compare = String.compare
  end)
val funcNameToProc: frag M.map ref = ref M.empty
fun procEntryExit (funcName, {level=Level{parent, frame, levelRef}, body = bodyExp}) =
  let
    val body = T.MOVE(T.TEMP(F.V0), unEx(bodyExp))
    val proc = F.PROC{body=F.procEntryExit1(frame, body),frame=frame}
  in
    funcNameToProc := M.insert(!funcNameToProc, funcName, proc)
  end
  | procEntryExit (funcName, {level=BaseLevel, body}) = bugErr "cannot exit BaseLevel!"

(* Invoked only at the end of semant.sml, after all code segment and data segment have been added. *)
fun getResult () =
  let
    fun addProcToFragList (funcName, proc, procList) = proc :: procList
    val procList = M.foldli addProcToFragList [] (!funcNameToProc)
  in
    procList @ (!fragList)
  end

fun getStaticLink frame fp = F.exp (List.hd (F.formals frame)) fp

(* levelHelp(outermost, curLevel, T.TEMP F.FP) *)

(*(#parent decLevel, callLevel, fp)*)
fun levelHelp (BaseLevel, Level{parent, frame, levelRef}, fp) = levelHelp(BaseLevel, parent, getStaticLink frame fp)
  | levelHelp (decLevel as Level{levelRef=decRef, ...}, curLevel as Level{parent,frame,levelRef=curRef}, fp) = 
      if decRef = curRef 
      then fp
      else levelHelp(decLevel, parent, getStaticLink frame fp)
  | levelHelp (BaseLevel, BaseLevel, fp) = fp
  | levelHelp (decLevel, BaseLevel, fp) = (bugErr "call function at BaseLevel!"; fp)

(* for printtree.sml as input *)
fun transResExp exp = unNx(exp)

(* val simpleVar : Translate.access * level -> Tree.exp *)
fun transSimpleVar ((BaseLevel, _), _) = (error "Simple var should not be declared at BaseLevel"; Ex(T.CONST(0)))
  | transSimpleVar ((decLevel, faccess), curLevel) = Ex (F.exp faccess (levelHelp(decLevel, curLevel, T.TEMP F.FP)))

(* Interface reserved for semant. *)
fun transNil () = Ex(T.CONST(0))

fun transInt v = Ex(T.CONST(v))

fun boolToInt b = if b then 1 else 0
fun transBool v = Ex(T.CONST(boolToInt(v)))

val strLiteralMap : Temp.label S.table ref = ref S.empty (* <symbol, label> *)
fun transStr v =
  let
    val sym = S.symbol(v)
  in
    case S.look(!strLiteralMap, sym) of
      SOME(strLabel) => Ex(T.NAME(strLabel))
    | NONE =>
      let
        val strLabel = Temp.newlabel()
      in
      (
        strLiteralMap := S.enter(!strLiteralMap, sym, strLabel);
        labelStringMap := LabelStringMap.insert(!labelStringMap, S.name(strLabel), v);
        (*string literals placed at the end of the assembly*)
        fragList := !fragList@[F.STRING(strLabel, v)];
        Ex(T.NAME(strLabel))
      )
      end
  end

fun transBinop (A.PlusOp, Ex(T.CONST(v1)), Ex(T.CONST(v2))) = Ex(T.CONST(v1 + v2))
  | transBinop (A.PlusOp, Ex(T.CONST(0)), right) = right
  | transBinop (A.PlusOp, left, Ex(T.CONST(0))) = left
  | transBinop (A.PlusOp, left, right) = Ex(T.BINOP(T.PLUS, unEx(left), unEx(right)))

  | transBinop (A.MinusOp, Ex(T.CONST(v1)), Ex(T.CONST(v2))) = Ex(T.CONST(v1 - v2))
  | transBinop (A.MinusOp, left, Ex(T.CONST(0))) = left
  | transBinop (A.MinusOp, left, right) = Ex(T.BINOP(T.MINUS, unEx(left), unEx(right)))

  | transBinop (A.TimesOp, Ex(T.CONST(v1)), Ex(T.CONST(v2))) = Ex(T.CONST(v1 * v2))
  | transBinop (A.TimesOp, Ex(T.CONST(0)), right) = Ex(T.CONST(0))
  | transBinop (A.TimesOp, left, Ex(T.CONST(0))) = Ex(T.CONST(0))
  | transBinop (A.TimesOp, Ex(T.CONST(1)), right) = right
  | transBinop (A.TimesOp, left, Ex(T.CONST(1))) = left
  | transBinop (A.TimesOp, left, right) = Ex(T.BINOP(T.MUL, unEx(left), unEx(right)))

  | transBinop (A.DivideOp, Ex(T.CONST(_)), Ex(T.CONST(0))) = (error "Cannot divide by 0"; Ex(T.CONST(0)))
  | transBinop (A.DivideOp, Ex(T.CONST(v1)), Ex(T.CONST(v2))) = Ex(T.CONST(v1 div v2))
  | transBinop (A.DivideOp, Ex(T.CONST(0)), right) = Ex(T.CONST(0))
  | transBinop (A.DivideOp, left, right) = Ex(T.BINOP(T.DIV, unEx(left), unEx(right)))

  | transBinop (_) = (error "Compiler error: transBinop meets unexpected operator."; Ex(T.CONST(0)))

(* String variable comparisons should be completed via external calls, but currently only support tig_stringEqual at runtime.s. *)
fun transRelop (A.EqOp,  Ex(T.NAME(lab1)), Ex(T.NAME(lab2)), Types.STRING) = transBool(getStringLiteral(lab1) =  getStringLiteral(lab2))
  | transRelop (A.NeqOp, Ex(T.NAME(lab1)), Ex(T.NAME(lab2)), Types.STRING) = transBool(getStringLiteral(lab1) <> getStringLiteral(lab2))
  | transRelop (A.LtOp,  Ex(T.NAME(lab1)), Ex(T.NAME(lab2)), Types.STRING) = transBool(getStringLiteral(lab1) <  getStringLiteral(lab2))
  | transRelop (A.LeOp,  Ex(T.NAME(lab1)), Ex(T.NAME(lab2)), Types.STRING) = transBool(getStringLiteral(lab1) <= getStringLiteral(lab2))
  | transRelop (A.GtOp,  Ex(T.NAME(lab1)), Ex(T.NAME(lab2)), Types.STRING) = transBool(getStringLiteral(lab1) >  getStringLiteral(lab2))
  | transRelop (A.GeOp,  Ex(T.NAME(lab1)), Ex(T.NAME(lab2)), Types.STRING) = transBool(getStringLiteral(lab1) >= getStringLiteral(lab2))
  | transRelop (A.EqOp,  left, right, Types.STRING) = Ex(F.externalCall("tig_stringEqual", [unEx(left), unEx(right)]))
  | transRelop (A.NeqOp, left, right, Types.STRING) = Ex(F.externalCall("stringNotEqual", [unEx(left), unEx(right)]))
  | transRelop (A.LtOp,  left, right, Types.STRING) = Ex(F.externalCall("stringLessThan", [unEx(left), unEx(right)]))
  | transRelop (A.LeOp,  left, right, Types.STRING) = Ex(F.externalCall("stringLessEqual", [unEx(left), unEx(right)]))
  | transRelop (A.GtOp,  left, right, Types.STRING) = Ex(F.externalCall("stringGreaterThan", [unEx(left), unEx(right)]))
  | transRelop (A.GeOp,  left, right, Types.STRING) = Ex(F.externalCall("stringGreaterEqual", [unEx(left), unEx(right)]))
  | transRelop (A.EqOp,  Ex(T.CONST(val1)), Ex(T.CONST(val2)), ty) = transBool(val1 =  val2)
  | transRelop (A.NeqOp, Ex(T.CONST(val1)), Ex(T.CONST(val2)), ty) = transBool(val1 <> val2)
  | transRelop (A.LtOp,  Ex(T.CONST(val1)), Ex(T.CONST(val2)), ty) = transBool(val1 <  val2)
  | transRelop (A.LeOp,  Ex(T.CONST(val1)), Ex(T.CONST(val2)), ty) = transBool(val1 <= val2)
  | transRelop (A.GtOp,  Ex(T.CONST(val1)), Ex(T.CONST(val2)), ty) = transBool(val1 >  val2)
  | transRelop (A.GeOp,  Ex(T.CONST(val1)), Ex(T.CONST(val2)), ty) = transBool(val1 >= val2)
  (* | transRelopImpl (oper, left, right, _) = Ex(unEx(Cx(fn (t, f) => T.CJUMP(operNode, left, right, t, f)))) *)
  (* Note: test46.tig: b = nil; will be compiled to a label, instead of EqOp. *)
  | transRelop (A.EqOp,  left, right, _) = Cx(fn (t, f) => T.CJUMP(T.EQ, unEx(left), unEx(right), t, f))
  | transRelop (A.NeqOp, left, right, _) = Cx(fn (t, f) => T.CJUMP(T.NE, unEx(left), unEx(right), t, f))
  | transRelop (A.LtOp,  left, right, _) = Cx(fn (t, f) => T.CJUMP(T.LT, unEx(left), unEx(right), t, f))
  | transRelop (A.LeOp,  left, right, _) = Cx(fn (t, f) => T.CJUMP(T.LE, unEx(left), unEx(right), t, f))
  | transRelop (A.GtOp,  left, right, _) = Cx(fn (t, f) => T.CJUMP(T.GT, unEx(left), unEx(right), t, f))
  | transRelop (A.GeOp,  left, right, _) = Cx(fn (t, f) => T.CJUMP(T.GE, unEx(left), unEx(right), t, f))
  | transRelop (_) = (error "Compiler error: transRelop meets unexpected operator."; Ex(T.CONST(0)))

fun transAssign (left, right) =
  let
    val l = unEx(left)
    val r = unEx(right)
  in
    Nx(T.MOVE(l, r))
  end

fun transIfThen (testExp, thenExp) =
  if isConstantValTrue(testExp) then thenExp
  else if isConstantValFalse(testExp) then transNil()
  else
    let
      val test' = unCx(testExp)
      val then' = unEx(thenExp)
      val t = Temp.newlabel()
      val f = Temp.newlabel()
    in
      Nx(seq([
        test'(t, f),
        T.LABEL(t),
        T.EXP(then'),
        T.LABEL(f)
      ]))
    end

fun transIfThenElse (testExp, thenExp, elseExp) =
  if (isConstantValFalse(testExp)) then elseExp
  else if (isConstantValTrue(testExp)) then thenExp
  else
    let
      val test' = unCx(testExp)
      val then' = unEx(thenExp)
      val else' = unEx(elseExp)
      val t = Temp.newlabel()
      val f = Temp.newlabel()
      val endLabel = Temp.newlabel()
      val r = Temp.newtemp()
    in
      Ex(T.ESEQ(seq([
        test'(t, f),
        T.LABEL(t),
        T.MOVE(T.TEMP(r), then'),
        T.JUMP(T.NAME(endLabel), [endLabel]),
        T.LABEL(f),
        T.MOVE(T.TEMP(r), else'),
        T.LABEL(endLabel)
        ]),
        T.TEMP(r)
        ))
    end

fun transFor (idxExp, lowExp, highExp, bodyExp, breakLabel) =
  let
    val idx = unEx(idxExp)
    val lo = unEx(lowExp)
    val hi = unEx(highExp)
    val body = unNx(bodyExp)
    val hiReg = Temp.newtemp()
    val bodyLabel = Temp.newlabel()
  in
    if (isConstant(lowExp) andalso isConstant(highExp) andalso getConstVal(lowExp) > getConstVal(highExp)) then transNil()
    else if (isConstant(lowExp) andalso isConstant(highExp) andalso getConstVal(lowExp) = getConstVal(highExp)) then
      Nx(seq([
        T.MOVE(idx, lo),
        body
      ]))
    else if (isConstant(lowExp) andalso isConstant(highExp) andalso getConstVal(lowExp) + 1 = getConstVal(highExp)) then
      Nx(seq([
        T.MOVE(idx, lo),
        body,
        T.MOVE(idx, hi),
        body
      ]))
    else
      Nx(seq([
        T.MOVE(idx, lo),
        T.CJUMP(T.LE, idx, hi, bodyLabel, breakLabel),
        T.LABEL(bodyLabel),
        body,
        T.MOVE(idx, T.BINOP(T.PLUS, idx, T.CONST(1))),
        T.CJUMP(T.LE, idx, hi, bodyLabel, breakLabel),
        T.LABEL(breakLabel)
      ]))
  end

fun transWhile (testExp, bodyExp, breakLabel) =
  if (isConstantValFalse(testExp)) then transNil()
  else
    let
      val test = unCx(testExp)
      val body = unNx(bodyExp)
      val t = Temp.newlabel()
    in
      Nx(seq([
        test(t, breakLabel),
        T.LABEL(t),
        body,
        test(t, breakLabel),
        T.LABEL(breakLabel)
      ]))
    end

fun transBreak NONE = (error "Compiler error: transBreak should guarenteed be called while nestedDepth > 0"; Nx(T.EXP(T.CONST(0))))
  | transBreak (SOME breakLabel) = Nx(T.JUMP(T.NAME(breakLabel), [breakLabel]))

(* Get address of addr[offset] *)
(* Temp.temp * Tree.exp -> Tree.exp *)
fun getMemAddr (addr: Temp.temp, offset: Tree.exp) = T.MEM(T.BINOP(T.PLUS, T.TEMP(addr), offset))

(* Assign value to memory address. addr *)
(* Tree.exp * Tree.exp -> T.stm *)
fun assignMemVal (addr: Tree.exp, value: Tree.exp) = T.MOVE(T.MEM(addr), value)

(*
  1. Create array via external call initArray(size, initVal)
  2. Allocate (actual_size + 1) wordSize, and set the first word value as size
  3. Return address is arrAddr
*)
fun transMkArray (sizeExp, initExp) =
  let
    val size = unEx(sizeExp)
    val init = unEx(initExp)
    val arrAddr = Temp.newtemp()
    val sizeArg =
      if (isConstant(sizeExp)) then T.CONST(getConstVal(sizeExp) + 1)
      else T.BINOP(T.PLUS, size, T.CONST(1))
  in
    Ex(T.ESEQ(seq([
      T.MOVE(T.TEMP(arrAddr), F.externalCall("tig_initArray", [sizeArg, init])),
      (* assignMemVal(T.TEMP(arrAddr), size) *)
      T.MOVE(T.MEM(T.TEMP(arrAddr)), size)
    ]),
    T.TEMP(arrAddr)
    ))
  end

fun transMkRecord (fieldList: exp list) =
  let
    val fieldLen = List.length fieldList
    val addr = Temp.newtemp()
    fun assignMem (exp, (idx, l)) =
      let

        (* getMemAddr: Temp.temp * Tree.exp -> Tree.exp *)
        (* assignMemVal: Tree.exp * Tree.exp -> T.stm *)
        val getMemAddr' = getMemAddr(addr, T.CONST(idx * F.wordSize))
        val assignMemVal' = T.MOVE(getMemAddr', unEx(exp))
      in
        (idx + 1, l@[assignMemVal'])
      end
    val (_, assignInstru) = foldl assignMem (0, []) fieldList
    val allocInstru = T.MOVE(T.TEMP(addr), F.externalCall("tig_allocRecord", [T.CONST(fieldLen * F.wordSize)]))
  in
    Ex(T.ESEQ(
      seq(allocInstru::assignInstru),
      T.TEMP(addr)
    ))
  end

fun transLet (decExpList, bodyExp) =
  let
    val decStmList = map unNx decExpList
    val body = unEx(bodyExp)
  in
    Ex(T.ESEQ(seq(decStmList), body))
  end

fun transVarDec ((_, frameAccess), initExp) =
  let
    val init = unEx(initExp)
  in
    Nx(T.MOVE(F.exp(frameAccess)(T.TEMP(F.FP)), init))
  end

(* callLevel, decLevel *)
fun transCall (curLevel, BaseLevel, funcLabel, argExpList) =
    (*Ex(T.CALL(T.NAME(funcLabel), levelHelp(outermost, curLevel, T.TEMP F.FP) :: (map unEx argExpList)))*)
    Ex(T.CALL(T.NAME(funcLabel), (map unEx argExpList)))
  | transCall (curLevel, Level{parent, ...}, funcLabel, argExpList) =
    Ex(T.CALL(T.NAME(funcLabel), levelHelp(parent, curLevel, T.TEMP F.FP) :: (map unEx argExpList)))

fun transSubscript (var, index) =
  let
    val arrReg = Temp.newtemp() (* address of array *)
    val idxReg = Temp.newtemp()
    val suc1Label = Temp.newlabel() (* label indicates idx >= 0 *)
    val suc2Label = Temp.newlabel() (* label indicates idx >= 0 && idx < size *)
    val failLabel = Temp.newlabel()

    val offset = (* includes extra one-wordSize memory for array size *)
      if (isConstant(index)) then T.CONST((getConstVal(index) + 1) * F.wordSize)
      else T.BINOP(T.MUL, T.CONST(F.wordSize), T.BINOP(T.PLUS, unEx(index), T.CONST(1)))
  in
    Ex(T.ESEQ(seq([
      T.MOVE(T.TEMP(idxReg), unEx(index)),
      T.MOVE(T.TEMP(arrReg), unEx(var)),
      T.CJUMP(T.GE, T.TEMP(idxReg), T.CONST(0), suc1Label, failLabel), (* bound check: idx >= 0 *)
      T.LABEL(suc1Label),
      T.CJUMP(T.LT, T.TEMP(idxReg), T.MEM(T.TEMP(arrReg)), suc2Label, failLabel), (* bound check: idx < size *)
      T.LABEL(failLabel),
      T.EXP(F.externalCall("exit", [T.CONST(1)])),
      T.LABEL(suc2Label)
      ]),
      T.MEM(T.BINOP(T.PLUS, T.TEMP(arrReg), offset))
      ))
  end

fun transField (var, offset) = 
  Ex(T.MEM(T.BINOP(T.PLUS, unEx(var), T.CONST(F.wordSize * offset))))

fun transSeq [] = (bugErr "transSeq expList should not be empty"; Ex(T.CONST(0)))
  | transSeq (expList: exp list) =
    let
      val expLen = List.length(expList)
      val expList' = List.take(expList, expLen - 1)
      val stmList = map unNx expList'
    in
      Ex(T.ESEQ(seq(stmList), unEx(List.last(expList))))
    end

end
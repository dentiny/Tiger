(*
  To test:
  CM.make "souces.cm";
  Main.main "../../testcases/test38.tig";
*)

structure Semant : SEMANT =
struct
    structure A = Absyn
    structure S = Symbol
    structure E = Env
    structure T = Types
    structure Tr = Translate

    structure Key =
      struct
        type ord_key = string
        val compare = String.compare
      end
    structure StringSet = RedBlackSetFn (Key)

    (* used in loop: for, while, break *)
    val nestedDepth = ref 0

    (* for loop var cannot be assigned, and for loop could be nested *)
    val loopVarList: Symbol.symbol list ref = ref []

    val error = ErrorMsg.error
    (*fun debug pos str = ErrorMsg.error pos ("[Debug]"^str)*)
    fun debug pos str = ()
    fun debugIR str = ErrorMsg.error 0 ("[IR Debug]"^str)
    fun bugErr pos str = error pos ("[Compiler error]" ^ str)

    fun isLoopVar (id) = isSome(List.find (fn loopVar => id = loopVar) (!loopVarList))

    fun addEntry((curSym, curType), curTenv) = S.enter(curTenv, curSym, curType)

    fun getArrayType(T.ARRAY(arrType, arrRef), pos) = arrType
      | getArrayType (_, pos) = (error pos "Var is not array type"; T.UNIT)

    (* Recursively get past all NAME, for other types just return. *)
    fun actual_ty (tenv, T.NAME(sym, tyRef), pos) =
      (
        case (!tyRef) of
        SOME typ => actual_ty(tenv, typ, pos)
        | NONE => (error pos ((S.name sym) ^ " hasn't been completely defined"); T.UNIT)
      )
      | actual_ty (tenv, typ, pos) = typ

    (* Get the actual type of symbol, call actual_ty() internally. *)
    fun getType(tenv, sym, pos) =
        case S.look(tenv, sym) of 
            SOME typ => actual_ty(tenv, typ, pos)
            | NONE => (error pos ("No such type " ^ S.name sym); T.UNIT)

    fun isSameType (tenv, T.NAME(typ1), T.NAME(typ2), pos) = isSameType(tenv, actual_ty(tenv, T.NAME(typ1), pos), actual_ty(tenv, T.NAME(typ2), pos), pos)
      | isSameType (tenv, T.NAME(typ1), typ2, pos) = isSameType(tenv, actual_ty(tenv, T.NAME(typ1), pos), typ2, pos)
      | isSameType (tenv, typ1, T.NAME(typ2), pos) = isSameType(tenv, typ1, actual_ty(tenv, T.NAME(typ2), pos), pos)
      | isSameType (tenv, T.ARRAY(_, arrRef1), T.ARRAY(_, arrRef2), pos) = arrRef1 = arrRef2
      | isSameType (tenv, T.RECORD(_, recRef1), T.RECORD(_, recRef2), pos) = recRef1 = recRef2
      | isSameType (tenv, T.NIL, T.RECORD(_, _), pos) = true
      | isSameType (tenv, T.RECORD(_, _), T.NIL, pos) = true
      | isSameType (tenv, typ1, typ2, pos) = typ1 = typ2

    (* Assert expression type *)
    fun assertInt (tenv, ty, pos) =
      if (isSameType(tenv, ty, T.INT, pos)) then ()
      else error pos "integer required"

    fun assertUnit (tenv, ty, pos) =
      if (isSameType(tenv, ty, T.UNIT, pos)) then ()
      else error pos "unit required"

    fun assertNotNil (T.NIL, pos) = error pos "should not be nil"
      | assertNotNil (_) = ()
    
    fun transExp(curLevel, venv, tenv, exp, breakLabel) =
      let 
        fun trexp (A.NilExp) = {exp = Tr.transNil() , ty = T.NIL}
          | trexp (A.IntExp(v)) = {exp = Tr.transInt(v), ty = T.INT}
          | trexp (A.StringExp(v, _)) = {exp = Tr.transStr(v), ty = T.STRING}
          | trexp (A.VarExp(v)) = trvar(v)

          (*
            1. Get current new tenv and venv via transDecs.
            2. Get instruction for all declarations:
              for variable declaration, add as runtime instructions;
              for type declaration, just use for type checking;
              for function declaration, add them to code fragment(fraglist at translate.sml)
            3. Type check body in the new tenv and venv.
            4. Get instruction for body.
          *)
          | trexp(A.LetExp{decs, body, pos}) =
              let 
                val {venv = venv',tenv = tenv', exp = decExpList} = transDecs(curLevel, venv, tenv, decs, [], breakLabel)
                val {exp = bodyExp, ty = bodyTy} = transExp(curLevel, venv', tenv', body, breakLabel)
              in
                {exp = Tr.transLet(decExpList, bodyExp), ty = bodyTy}
              end

          | trexp (A.OpExp{left, oper = A.PlusOp, right, pos}) =
              let
                val {exp = leftExp, ty = leftTy} = trexp(left)
                val {exp = rightExp, ty = rightTy} = trexp(right)
              in
                (
                  assertInt(tenv, leftTy, pos);
                  assertInt(tenv, rightTy, pos);
                  {exp = Tr.transBinop(A.PlusOp, leftExp, rightExp), ty = T.INT}
                )
              end

          | trexp (A.OpExp{left, oper = A.MinusOp, right, pos}) =
              let
                val {exp = leftExp, ty = leftTy} = trexp(left)
                val {exp = rightExp, ty = rightTy} = trexp(right)
              in
                (
                  assertInt(tenv, leftTy, pos);
                  assertInt(tenv, rightTy, pos);
                  {exp = Tr.transBinop(A.MinusOp, leftExp, rightExp), ty = T.INT}
                )
              end

          | trexp (A.OpExp{left, oper = A.TimesOp, right, pos}) =
            let
              val {exp = leftExp, ty = leftTy} = trexp(left)
              val {exp = rightExp, ty = rightTy} = trexp(right)
            in
              (
                assertInt(tenv, leftTy, pos);
                assertInt(tenv, rightTy, pos);
                {exp = Tr.transBinop(A.TimesOp, leftExp, rightExp), ty = T.INT}
              )
            end

          | trexp (A.OpExp{left, oper = A.DivideOp, right, pos}) =              
              let
                val {exp = leftExp, ty = leftTy} = trexp(left)
                val {exp = rightExp, ty = rightTy} = trexp(right)
              in
                (
                  assertInt(tenv, leftTy, pos);
                  assertInt(tenv, rightTy, pos);
                  {exp = Tr.transBinop(A.DivideOp, leftExp, rightExp), ty = T.INT}
                )
              end

          | trexp (A.OpExp{left, oper = A.LtOp, right, pos}) =
              let
                val {exp = leftExp, ty = tyLeft} = trexp(left)
                val {exp = rightExp, ty = tyRight} = trexp(right)
              in
                if isSameType(tenv, tyLeft, tyRight, pos) andalso (tyLeft = T.INT orelse tyLeft = T.STRING) 
                then {exp = Tr.transRelop(A.LtOp, leftExp, rightExp, tyLeft), ty = T.INT}
                else (error pos "Comprision operands type mismatch"; {exp = Tr.transNil(), ty = T.UNIT})
              end
          
          | trexp (A.OpExp{left, oper = A.LeOp, right, pos}) =
              let
                val {exp = leftExp, ty = tyLeft} = trexp(left)
                val {exp = rightExp, ty = tyRight} = trexp(right)
              in
                if isSameType(tenv, tyLeft, tyRight, pos) andalso (tyLeft = T.INT orelse tyLeft = T.STRING) 
                then {exp = Tr.transRelop(A.LeOp, leftExp, rightExp, tyLeft), ty = T.INT}
                else (error pos "Comprision operands type mismatch"; {exp = Tr.transNil(), ty = T.UNIT})
              end

          | trexp (A.OpExp{left, oper = A.GtOp, right, pos}) =
              let
                val {exp = leftExp, ty = tyLeft} = trexp(left)
                val {exp = rightExp, ty = tyRight} = trexp(right)
              in
                if isSameType(tenv, tyLeft, tyRight, pos) andalso (tyLeft = T.INT orelse tyLeft = T.STRING) 
                then {exp = Tr.transRelop(A.GtOp, leftExp, rightExp, tyLeft), ty = T.INT}
                else (error pos "Comprision operands type mismatch"; {exp = Tr.transNil(), ty = T.UNIT})
              end

          | trexp (A.OpExp{left, oper = A.GeOp, right, pos}) =
              let
                val {exp = leftExp, ty = tyLeft} = trexp(left)
                val {exp = rightExp, ty = tyRight} = trexp(right)
              in
                if isSameType(tenv, tyLeft, tyRight, pos) andalso (tyLeft = T.INT orelse tyLeft = T.STRING) 
                then {exp = Tr.transRelop(A.GeOp, leftExp, rightExp, tyLeft), ty = T.INT}
                else (error pos "Comprision operands type mismatch"; {exp = Tr.transNil(), ty = T.UNIT})
              end

          | trexp (A.OpExp{left, oper = A.EqOp, right, pos}) =
              let
                val {exp = leftExp, ty = tyLeft} = trexp(left)
                val {exp = rightExp, ty = tyRight} = trexp(right)
              in
                if isSameType(tenv, tyLeft, tyRight, pos)
                then {exp = Tr.transRelop(A.EqOp, leftExp, rightExp, tyLeft), ty = T.INT}
                else (error pos "Equality check operands type mismatch"; {exp = Tr.transNil(), ty = T.UNIT})
              end
          
          | trexp (A.OpExp{left, oper = A.NeqOp, right, pos}) =
              let
                val {exp = leftExp, ty = tyLeft} = trexp(left)
                val {exp = rightExp, ty = tyRight} = trexp(right)
              in
                if isSameType(tenv, tyLeft, tyRight, pos)
                then {exp = Tr.transRelop(A.NeqOp, leftExp, rightExp, tyLeft), ty = T.INT}
                else (error pos "Equality check operands type mismatch"; {exp = Tr.transNil(), ty = T.UNIT})
              end

          | trexp (A.AssignExp{var, exp, pos}) = 
              let
                val {exp = leftExp, ty = ty1} = trvar(var)
                val {exp = rightExp, ty = ty2} = trexp(exp)
              in
                case var of
                  A.SimpleVar(sym, _) => if (isLoopVar(sym)) then error pos "Loop variable cannot be assigned" else ()
                | _ => ();
                if isSameType(tenv, ty1, ty2, pos) then ()
                else error pos "Variable and expression type mismatch";
                {exp = Tr.transAssign(leftExp, rightExp), ty = T.UNIT}
              end

          | trexp (A.IfExp{test, then', else', pos}) =
            let
              val {exp = testExp, ty = testTy} = trexp(test)
              val {exp = thenExp, ty = thenTy} = trexp(then')
            in
            (
              assertInt(tenv, testTy, pos);
              case else' of
                NONE =>
                (
                  assertUnit(tenv, thenTy, pos);
                  {exp = Tr.transIfThen(testExp, thenExp), ty = T.UNIT}
                )
              | SOME(elseVal) =>
                  let
                    val {exp = elseExp, ty = elseTy} = trexp(elseVal)
                  in
                    if isSameType(tenv, thenTy, elseTy, pos) then ()
                    else error pos "The type of then and else mismatch";
                    {exp = Tr.transIfThenElse(testExp, thenExp, elseExp), ty = thenTy}
                  end
            )
            end

          | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            let
              val {exp = loExp, ty = loTy} = trexp(lo)
              val {exp = hiExp, ty = hiTy} = trexp(hi)
              val () = nestedDepth := !nestedDepth + 1
              val () = loopVarList := var :: (!loopVarList)
              val idxAccess = Tr.allocLocal(curLevel)(!escape)
              val tempVenv = S.enter(venv, var, E.VarEntry{access = idxAccess, ty = T.INT})
              val breakLabel = Temp.newlabel()
              val {exp = bodyExp, ty = bodyTy} = transExp(curLevel, tempVenv, tenv, body, SOME(breakLabel))
              val idxExp = Tr.transSimpleVar(idxAccess, curLevel)
            in
            (
              assertInt(tenv, loTy, pos);
              assertInt(tenv, hiTy, pos);
              if isSameType(tenv, bodyTy, T.UNIT, pos) then ()
              else error pos "Body of the for loop should be unit";
              nestedDepth := !nestedDepth - 1;
              loopVarList := List.drop(!loopVarList, 1);
              {exp = Tr.transFor(idxExp, loExp, hiExp, bodyExp, breakLabel), ty = T.UNIT}
            )
            end

          | trexp (A.WhileExp{test, body, pos}) =
            let
              val breakLabel = Temp.newlabel()
              val () = nestedDepth := !nestedDepth + 1
              val {exp = testExp, ty = testTy} = trexp(test)
              val {exp = bodyExp, ty = bodyTy} = transExp(curLevel, venv, tenv, body, SOME(breakLabel))
            in
            (
              assertInt(tenv, testTy, pos);
              if isSameType(tenv, bodyTy, T.UNIT, pos) then ()
              else error pos "Body of the while loop should be unit";
              nestedDepth := !nestedDepth - 1;
              {exp = Tr.transWhile(testExp, bodyExp, breakLabel), ty = T.UNIT}
            )
            end

          (*
            1. nestedDepth is only checked in break expression, but updated at for and while loop.
            2. Every transExp has am optional breakLabel which is only assigned dealing with while and for body. 
          *)
          | trexp (A.BreakExp(pos)) =
            (
              if (!nestedDepth <= 0) then (error pos "Break should be used in while or for loop"; {exp = Tr.transNil(), ty = T.UNIT})
              else {exp = Tr.transBreak(breakLabel), ty = T.UNIT}
            )

          | trexp (A.SeqExp(expSeq)) =
            let
              fun expSeqHelper [] = [{exp = Tr.transNil(), ty = T.UNIT}]
                | expSeqHelper [(exp, pos)] = [trexp(exp)]
                | expSeqHelper ((exp, pos)::l) = trexp(exp)::expSeqHelper(l)
              val expListTy = expSeqHelper(expSeq)
              val (expList: Tr.exp list) = map #exp expListTy
              val RT = #ty(List.last(expListTy))
            in
              {exp = Tr.transSeq(expList), ty = RT}
            end

          | trexp (A.CallExp{func, args, pos}) =
            (
              (*error pos ("[leleflag2]:" ^ (S.name func) ^ "\n");*)
              case S.look(venv, func) of 
              SOME(E.FunEntry{level = decLevel, label, formals, result}) => 
              let
                fun checkFuncType([], []) = ()
                  | checkFuncType(arg::argList, formal::formalList) =
                    if isSameType(tenv, #ty (trexp(arg)), formal, pos) 
                    then checkFuncType(argList, formalList)
                    else error pos ("Unmatched argument type with formal in function " ^ (S.name func))
                  | checkFuncType(_, _) = error pos ("Incorrect arg length for function:" ^ S.name func)
                val argExpList = map (fn arg => #exp(trexp(arg))) args
              in
              (
                checkFuncType(args, formals);
                {exp = Tr.transCall(curLevel, decLevel, label, argExpList), ty = result}
              )
              end
            | _ => (error pos ("Undefined function " ^ S.name func); {exp = Tr.transNil(), ty = T.UNIT})
            )

          | trexp (A.RecordExp{fields, typ, pos}) =
            (
              case getType(tenv, typ, pos) of
                T.RECORD(recordType) =>
                  let
                    val symList = #1 recordType
                    val symMap = ref S.empty (* temporary map to store input record members without duplication *)

                    fun symMatch (sym, exp, pos) = 
                      let
                        fun isTypeMatched definedType = isSameType(tenv, #ty (trexp(exp)), definedType, pos)
                        val isSymbolInDefined = List.exists (fn (definedSymbol, definedType) => sym = definedSymbol andalso isTypeMatched definedType) symList
                        val isSymbolUnique = not(isSome(S.look(!symMap, sym)))
                      in
                        case (isSymbolInDefined, isSymbolUnique) of
                          (true, true) => (symMap := S.enter (!symMap, sym, T.UNIT); true)
                        | (true, false) => (error pos ("Element not unique in record declaration: " ^ (S.name sym)); false)
                        | (false, true) => (error pos ("Symbol or type mismatch predefined type: " ^ (S.name sym)); false)
                        | (_, _) => false
                      end

                    val filteredList = List.filter symMatch fields (* fields: (symbol * exp * pos) list *)
                  in
                  (
                    if List.length(filteredList) = List.length(symList) 
                    then {exp = Tr.transMkRecord(map (fn (sym, exp, pos) => #exp(trexp(exp))) fields), ty = T.RECORD recordType}
                    else (error pos "Record expression error"; {exp = Tr.transNil(), ty = T.UNIT})
                  )
                    
                  end
                | _ => (error pos ("No such type " ^ S.name typ); {exp = Tr.transNil(), ty = T.UNIT})
            )

          | trexp (A.ArrayExp{typ, size, init, pos}) =
            let
              val {exp = sizeExp, ty = sizeTy} = trexp(size)
              val {exp = initExp, ty = initTy} = trexp(init)
              val arrayTy = getType(tenv, typ, pos)
              val elementTy = getArrayType(arrayTy, pos)
            in
              assertInt(tenv, sizeTy, pos);
              if isSameType(tenv, initTy, elementTy, pos)
              then {exp = Tr.transMkArray(sizeExp, initExp), ty = arrayTy}
              else (error pos ("Wrong init type for array " ^ (S.name typ)); {exp = Tr.transNil(), ty = T.UNIT})
            end

        and 

          trvar (A.SimpleVar(id, pos)) =
          (
            case S.look(venv, id) of 
                SOME(E.VarEntry{access, ty}) => {exp = Tr.transSimpleVar(access, curLevel), ty = actual_ty(tenv, ty, pos)}
              | SOME(E.FunEntry{...}) => (error pos "Function called in the wrong place"; {exp = Tr.transNil(), ty = T.INT})
              | NONE => (error pos ("Undefined variable " ^ S.name id); {exp = Tr.transNil(), ty = T.INT})
          )
        
        | trvar (A.SubscriptVar(var, exp, pos)) =
          let 
            val {exp = varExp, ty = varType} = trvar(var)
            val {exp = indexExp, ty = indexType} = trexp(exp)
            val arrType = getArrayType(actual_ty(tenv, varType, pos), pos)
          in
            (
              assertInt(tenv, indexType, pos);
              {exp = Tr.transSubscript(varExp, indexExp), ty = actual_ty(tenv, arrType, pos)}
            )
          end

        | trvar (A.FieldVar(var, symbol, pos)) =
            let
              val {exp = varExp, ty = varType} = trvar(var)
            in
              case actual_ty(tenv, varType, pos) of
                T.RECORD (fieldList, _) => 
                  let
                    fun findIdx([], s, count) = 
                          (error pos ("no such field in record"); {exp = Tr.transNil(), ty = T.UNIT})
                      | findIdx((s1,ty)::l, s, count) = 
                          if (s1 = s)
                          then {exp = Tr.transField(varExp, count), ty = ty} 
                          else findIdx(l, s, count+1)
                  in
                    findIdx(fieldList, symbol, 0)
                  end
              | _ => (error pos ("Should be record."); {exp = Tr.transNil(), ty = T.UNIT})
            end

      in
        trexp exp
      end

    and transDecs (curLevel, venv, tenv, [], decExpList, breakLabel) = {venv = venv, tenv = tenv, exp = decExpList}
      | transDecs (curLevel, venv, tenv, decs, decExpList, breakLabel) =
        let
          fun trdec (A.VarDec{name, escape, typ = NONE, init, pos}, {venv, tenv, exp = decExpList}) =
            let
              val {exp = initExp, ty = initTy} = transExp(curLevel, venv, tenv, init, breakLabel)
              val (varAccess: Tr.access) = Tr.allocLocal(curLevel)(!escape)
              val venv' = S.enter(venv, name, E.VarEntry{access = varAccess, ty = initTy})
            in
            (
              assertNotNil(initTy, pos);
              {tenv = tenv, venv = venv', exp = decExpList@[Tr.transVarDec(varAccess, initExp)]}
            )
            end

            | trdec (A.VarDec{name, escape, typ = SOME(decTy, decTyPos), init, pos}, {venv, tenv, exp = decExpList}) =
                let 
                  val {exp = initExp, ty = ty} = transExp(curLevel, venv, tenv, init, breakLabel)
                  val (varAccess: Tr.access) = Tr.allocLocal(curLevel)(!escape)
                  val decType = getType(tenv, decTy, pos)
                in
                  if isSameType(tenv, ty, decType, pos) then 
                    {tenv = tenv, venv = S.enter(venv, name, E.VarEntry{access = varAccess, ty = ty}),
                      exp = decExpList@[Tr.transVarDec(varAccess, initExp)]}  
                  else 
                      (
                        error pos ("Type wrong. Declared as " ^ S.name decTy); 
                        {tenv = tenv, venv = venv, exp = decExpList}
                      )
                end

            (*
              Error cases for type declaration:
              1) no circular dependency, eg:
                  type a = b;
                  type b = a;
              2) redeclaration
              3) should be deterministic, eg:
                  type a = b;
              *)
            | trdec (A.TypeDec[], {venv, tenv, exp = decExpList}) = (bugErr 0 "Type declaration list shouldn't be empty"; {venv = venv, tenv = tenv, exp = decExpList})
            | trdec (A.TypeDec(tydecs), {venv, tenv = globalTenv, exp = decExpList}) = (* tydecs: {name: symbol, ty: ty, pos: pos} list *)
                let
                  (*
                    Add types into globalTenv and check redeclaration. Currently all types(A.NameTy, A.RecordTy, A.ArrayTy) unknown
                    is Temporarily assigned T.NAME(dependent type, ref NONE), and will be correctly in the second iteration.
                  *)
                  val visited = ref StringSet.empty
                  fun addTypeSymbolAndCheckRedec({name, ty: A.ty, pos}, tenv) =
                    if StringSet.member(!visited, S.name name) then (error pos ("Type " ^ (S.name name) ^ " redeclaration."); tenv)
                    else
                    (
                      visited := StringSet.add(!visited, S.name name);
                      S.enter(tenv, name, transTy(globalTenv, ty))
                    )
                  val tenv' = foldl addTypeSymbolAndCheckRedec globalTenv tydecs

                  fun updateReferenceSymbol({name, ty: A.ty, pos}, tenv) =
                    let
                      (* used to detect and avoid loop exists in type dependency lineage, reinitialized every tydec *)
                      val visited = ref StringSet.empty

                      (*
                        Currently resolved symbols are not recorded for code simplicity, so types within a dependency lineage will be
                        recalculated. eg: a -> b -> c, if a is passed in after b and c has been resolved or bug reported, all three will
                        go through an entire procedure. Considering type declaration and alias shouldn't be much, it's reasonable somewhat.
                      *)
                      fun updateReferenceHelper(sym) =
                        if (StringSet.member(!visited, S.name sym)) then (error pos "Loop exists in type declaration"; [(sym, T.UNIT)])
                        else
                        (
                          visited := StringSet.add(!visited, S.name sym);
                          case S.look(tenv', sym) of
                            NONE => (bugErr pos ((S.name sym) ^ " doesn't exists in tenv."); [(sym, T.UNIT)])

                            (*
                              array: T.ARRAY(T.NAME(dependentSymbol, symRef), arrRef)
                              record: T.RECORD(elemList, recRef) -> {elemSym: elemTyp}
                              How T.ARRAY and T.RECORD handles its dependent type:
                              1) if it appears at globalTenv, then directly settled down at transTy
                              2) otherwise simple assign it as T.NAME(dependentSym, ref). It could be illegal, eg:
                                - type myRecord = {mem: myType}, but it's never alias elsewhere, will be checked first whether in localTenv
                                - type myType = myType, type myRecord = {mem: myType}; assume type valid here, but will report error at NameTy
                            *)
                          | SOME(T.ARRAY(T.NAME(dependentSymbol, symRef), arrRef)) =>
                            (
                              case S.look(tenv', dependentSymbol) of
                                NONE => (error pos ("Element type " ^ (S.name dependentSymbol) ^ " of array type " ^ (S.name sym) ^ " cannot be resolved."); [(sym, T.UNIT)])
                              | SOME(dependentSymbolType) =>
                                (
                                  symRef := SOME(dependentSymbolType);
                                  [(sym, T.ARRAY(T.NAME(dependentSymbol, symRef), arrRef))]
                                )
                            )
                          | SOME(T.ARRAY(arrTy, arrRef)) => [(sym, T.ARRAY(arrTy, arrRef))]
                          | SOME(T.RECORD(elemList, recRef)) => (* (Symbol.symbol * ty) list * unique *)
                            let
                              fun updateRecordReference ((elemSym, elemTyp)) =
                                case elemTyp of
                                  T.NAME(elemDependentSymbol, tyRef) =>
                                  (
                                    case S.look (tenv', elemDependentSymbol) of
                                      SOME (finalizedTyp) =>
                                        (
                                          tyRef := SOME(finalizedTyp);
                                          (elemSym, T.NAME(name, tyRef))
                                        )
                                      | NONE => (error pos ("Element type " ^ (S.name elemSym) ^ " of record type " ^ (S.name sym) ^ " cannot be resolved."); (elemSym, elemTyp))
                                  )
                                  | _ => (elemSym, elemTyp)
                              val updatedRecType = T.RECORD(map updateRecordReference elemList, recRef)
                            in
                              [(sym, updatedRecType)]
                            end
                          | SOME(T.NAME(dependentSym, nameRef)) => (* Symbol.symbol * ty option ref *)
                            (
                              case S.look(tenv', dependentSym) of
                                NONE => (error pos ("Symbol " ^ (S.name dependentSym) ^ " cannot be found in dependency graph, dependency lineage incomplete."); [(sym, T.UNIT)])
                              | SOME(T.NAME(_, _)) =>
                                let
                                  val tailRes = updateReferenceHelper(dependentSym)
                                  val tailTy = #2(hd(tailRes))
                                in
                                  [(sym, tailTy)]@tailRes
                                end
                              | SOME(ty) => [(sym, ty)]
                            )
                          | SOME(ty) => [(sym, ty)]
                        )
                      val symTyList = updateReferenceHelper(name)
                    in
                      foldl addEntry tenv symTyList
                    end
                  val tenv'' = foldl updateReferenceSymbol globalTenv tydecs
                in
                  {venv = venv, tenv = tenv'', exp = decExpList}
                end

            | trdec (A.FunctionDec[], {venv, tenv, exp = decExpList}) = (bugErr 0 "Function declaration list shouldn't be empty"; {venv = venv, tenv = tenv, exp = decExpList})
            | trdec (A.FunctionDec(fundecs), {venv, tenv, exp = decExpList}) =
              let
                val set = ref StringSet.empty
                fun addSymbolAndCheck (set, name, pos) =
                    if StringSet.member(set, S.name name)
                    then (error pos ("Duplicated type name in mutaul recursion: " ^ S.name name); set)
                    else StringSet.add(set, S.name name)
                fun transparam{name, escape, typ, pos} =
                    {name = name, ty = getType(tenv, typ, pos), escape = !escape}
                fun get_result_ty (result, pos) = case result of
                  SOME(rt, rtPos) => getType(tenv, rt, pos)
                  | NONE => T.UNIT

                (*
                  1. addSig: add function type into venv
                  2. checkBody: type check function, add function to code fragment
                  3. self-recursion requires two-phase iteration(add and check)
                  4. for a single function, it should have its unique level in both addSig and checkBody, for level traverse at Tr.levelHelp
                *)
                val levelMap = ref S.empty (* map function name(S.symbol) to level created *)

                fun addSig({name, params, body, pos, result}, venv) =
                  let
                    val params' = map transparam params
                    val _ = set := addSymbolAndCheck(!set, name, pos)
                    val newLabel = Temp.namedlabel(S.name name);
                    (*val _ = error pos ("[leleflag]:" ^ (S.name name) ^ "\n");*)
                    val newLevel = Tr.newLevel({parent = curLevel, name = newLabel, formals = map #escape params'})
                    val () = levelMap := S.enter(!levelMap, name, newLevel)
                  in
                    S.enter(venv, name, E.FunEntry{level = newLevel, label = newLabel, formals = map #ty params', result = get_result_ty(result, pos)})
                  end
                val venv' = foldl addSig venv fundecs

                fun checkBody({name, params, body, pos, result}, venv) =
                    let
                      val params' = map transparam params
                      val funLevel = valOf(S.look(!levelMap, name))
                      val formals = List.drop(Tr.formals funLevel, 1)
                      (*val _ = print("levelformals len:" ^ (Int.toString(List.length formals)) ^ "\n")
                      val _ = print("param' len:" ^ (Int.toString(List.length params')) ^ "\n")*)
                      fun enterparam (index, venv) =
                        if (index >= List.length(params')) then venv
                        else
                          let
                            val {name, ty, escape} = List.nth(params', index)
                            val formal = List.nth(formals, index)
                            val curVenv = S.enter(venv, name, E.VarEntry{access = formal, ty = ty})
                          in
                            enterparam(index + 1, curVenv)
                          end
                      val venv'' = enterparam(0, venv')
                      (* fun enterparam ({name, ty, escape}, venv) = S.enter(venv, name, E.VarEntry{access = Tr.allocLocal(funLevel)(escape), ty=ty})
                      val venv'' = foldl enterparam venv' params' *)
                      val {exp=bodyExp, ty=bodyTy} = transExp(funLevel, venv'', tenv, body, breakLabel)
                      val _ = if isSameType(tenv, bodyTy, get_result_ty(result, pos), pos) then ()
                              else error pos "function body and return type mismatch"
                      val _ = Tr.procEntryExit(S.name(name), {level=funLevel, body=bodyExp})
                   in
                       venv
                   end
                val venv'' = foldl checkBody venv fundecs
              in
                  {venv = venv', tenv = tenv, exp = decExpList}
              end
        in
          foldl trdec {venv = venv, tenv = tenv, exp = decExpList} decs (* decExpList stores instructions for declarations *)
        end

    and 

        (* Translate type declaration in AST into Type. *)
        transTy(tenv, A.NameTy(name, pos)) = 
          (
            case S.look(tenv, name) of
              SOME ty => ty
              | NONE => T.NAME(name, ref NONE)
          )

      | transTy(tenv, A.RecordTy fields) =
          let
            fun fieldToRecordTy{name, escape, typ, pos} = case S.look(tenv, typ) of
              SOME ty => (name, ty)
              | NONE => (name, T.NAME(typ, ref NONE))
          in
            T.RECORD((map fieldToRecordTy fields), ref())
          end

      | transTy(tenv, A.ArrayTy(sym, pos)) =
          (
            case S.look (tenv, sym) of 
              SOME ty => T.ARRAY(ty, ref())
            | NONE => T.ARRAY(T.NAME(sym, ref NONE), ref())
          )

    fun transProg(exp: A.exp) : Translate.frag list =
      let
        val startLabel = Temp.namedlabel("tig_main")
        val startLevel = Tr.newLevel({parent = Tr.outermost, name = startLabel, formals = []})
        (* val () = FindEscape.findEscape(exp) *)
        val exp' = #exp(transExp(startLevel, E.base_venv, E.base_tenv, exp, NONE (* breakLabel *) ))
        val () = Tr.procEntryExit("tig_main", {level = startLevel, body = exp'})
      in
        Tr.getResult()
      end
      
end
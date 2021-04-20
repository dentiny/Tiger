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

    structure Key =
      struct
        type ord_key = string
        val compare = String.compare
      end
    structure StringSet = RedBlackSetFn (Key)

    (* used in loop: for, while, break *)
    val nestedDepth = ref 0

    val error = ErrorMsg.error
    (*fun debug pos str = ErrorMsg.error pos ("[Debug]"^str)*)
    fun debug pos str = ()
    fun bugErr pos str = error pos ("[Compiler error]" ^ str)

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
    fun checkInt (tenv, {exp, ty}, pos) =
      if (isSameType(tenv, ty, T.INT, pos)) then ()
      else error pos "integer required"

    fun checkUnit (tenv, {exp, ty}, pos) =
      if (isSameType(tenv, ty, T.UNIT, pos)) then ()
      else error pos "unit required"

    fun assertNotNil (T.NIL, pos) = error pos "should not be nil"
      | assertNotNil (_) = ()
    
    fun transExp(venv, tenv, exp) =
      let 
        fun trexp (A.NilExp) = {exp = (), ty = T.NIL}
          | trexp (A.IntExp(v)) = {exp = (), ty = T.INT}
          | trexp (A.StringExp(v)) = {exp = (), ty = T.STRING}
          | trexp (A.VarExp(v)) = trvar(v)

          | trexp(A.LetExp{decs, body, pos}) =
              let 
                val {venv = venv',tenv = tenv'} = transDecs(venv, tenv, decs)
              in 
                transExp(venv', tenv', body)
              end

          | trexp (A.OpExp{left, oper = (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp), right, pos}) =
            (
              checkInt(tenv, trexp(left), pos);
              checkInt(tenv, trexp(right), pos);
              {exp = (), ty = T.INT}
            )

          | trexp (A.OpExp{left, oper = (A.LtOp | A.LeOp | A.GtOp | A.GeOp), right, pos}) =
            let
                val {exp = _, ty = tyLeft} = trexp(left)
                val {exp = _, ty = tyRight} = trexp(right)
            in
                if isSameType(tenv, tyLeft, tyRight, pos) andalso (tyLeft = T.INT orelse tyLeft = T.STRING) 
                then {exp = (), ty = T.INT}
                else (error pos "Comprision operands type mismatch"; {exp = (), ty = T.UNIT})
            end

          | trexp (A.OpExp{left, oper = (A.EqOp | A.NeqOp), right, pos}) =
            let
                val {exp = _, ty = tyLeft} = trexp(left)
                val {exp = _, ty = tyRight} = trexp(right)
            in
                if isSameType(tenv, tyLeft, tyRight, pos)
                then {exp = (), ty = T.INT}
                else (error pos "Equality check operands type mismatch"; {exp = (), ty = T.UNIT})
            end

          | trexp (A.AssignExp{var, exp, pos}) = 
              let
                val {exp = _, ty = ty1} = trvar(var)
                val {exp = _, ty = ty2} = trexp(exp)
              in
                if isSameType(tenv, ty1, ty2, pos) then ()
                else error pos "Variable and expression type mismatch";
                {exp = (), ty = T.UNIT}
              end

          | trexp (A.IfExp{test, then', else', pos}) =
            (
              checkInt(tenv, trexp(test), pos);
              case else' of
                NONE => 
                (
                  checkUnit(tenv, trexp(then'), pos);
                  {exp = (), ty = T.UNIT}
                )
              | SOME(elseVal) =>
                let
                  val {exp = _, ty = thenTy} = trexp(then')
                  val {exp = _, ty = elseTy} = trexp(elseVal)
                in
                  if isSameType(tenv, thenTy, elseTy, pos) then ()
                  else error pos "The type of then and else mismatch";
                  {exp = (), ty = thenTy}
                end
            )

          | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            (
              checkInt(tenv, trexp(lo), pos);
              checkInt(tenv, trexp(hi), pos);
              nestedDepth := !nestedDepth + 1;

              let
                val tempVenv = S.enter(venv, var, E.VarEntry{ty = T.INT})
                val {exp = _, ty = bodyTy} = transExp(tempVenv, tenv, body)
              in
                if isSameType(tenv, bodyTy, T.UNIT, pos) then ()
                else error pos "Body of the for loop should be unit";
                nestedDepth := !nestedDepth - 1;
                {exp = (), ty = T.UNIT}
              end
            )

          | trexp (A.WhileExp{test, body, pos}) =
            (
              checkInt(tenv, trexp(test), pos);
              nestedDepth := !nestedDepth + 1;

              let
                val {exp = _, ty = bodyTy} = trexp(body)
              in
                if isSameType(tenv, bodyTy, T.UNIT, pos) then ()
                else error pos "Body of the while loop should be unit";
                nestedDepth := !nestedDepth - 1;
                {exp = (), ty = T.UNIT}
              end
            )

          (* nestedDepth is only checked in break expression, but updated at for and while loop *)
          | trexp (A.BreakExp(pos)) =
            (
              if (!nestedDepth <= 0) then error pos "Break should be used in while or for loop"
              else ();
              {exp = (), ty = T.UNIT}
            )

          | trexp (A.SeqExp(expSeq)) =
            let
              fun expSeqHelper [] = {exp = (), ty = T.UNIT}
                | expSeqHelper [(exp, pos)] = trexp(exp)
                | expSeqHelper ((exp, pos)::l) = (trexp(exp); expSeqHelper(l))
            in
              expSeqHelper(expSeq)
            end

          | trexp (A.CallExp{func, args, pos}) =
            (
              case S.look(venv, func) of 
              SOME(E.FunEntry{formals, result}) => 
              let
                  fun checkFuncType([], []) = ()
                    | checkFuncType(arg::argList, formal::formalList) =
                      if isSameType(tenv, #ty (trexp(arg)), formal, pos) 
                      then checkFuncType(argList, formalList)
                      else error pos ("Unmatched argument type with formal in function " ^ (S.name func))
                    | checkFuncType(_, _) = error pos ("Incorrect arg length for function:" ^ S.name func)
              in
                  (checkFuncType(args, formals); {exp = (), ty = result})
              end
            | _ => (error pos ("Undefined function " ^ S.name func); 
                    {exp = (), ty = T.UNIT})
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
                    then {exp = (), ty = T.RECORD recordType}
                    else (error pos "Record expression error"; {exp = (), ty = T.UNIT})
                  )
                    
                  end
                | _ =>
                  (error pos ("No such type " ^ S.name typ);
                    {exp = (), ty = T.UNIT})
            )

          | trexp (A.ArrayExp{typ, size, init, pos}) =
            (
              checkInt(tenv, trexp(size), pos);
              let
                  val {exp = _, ty = initType} = trexp(init)
                  val arrayType = getType(tenv, typ, pos)
                  val elementType = getArrayType(arrayType, pos)
              in
                  if isSameType(tenv, initType, elementType, pos)
                  then {exp = (), ty = arrayType}
                  else (error pos ("Wrong init type for array " ^ (S.name typ)); {exp = (), ty = T.UNIT})
              end
            )

        and 

          trvar (A.SimpleVar(id, pos)) =
          (
            case S.look(venv, id) of 
                SOME(E.VarEntry{ty}) => {exp = (), ty = actual_ty(tenv, ty, pos)}
              | SOME(E.FunEntry{...}) => (error pos "Function called in the wrong place"; {exp = (), ty = T.INT})
              | NONE => (error pos ("Undefined variable " ^ S.name id); {exp = (), ty = T.INT})
          )
        
        | trvar (A.SubscriptVar(var, exp, pos)) =
          let 
            val {exp = _, ty = varType} = trvar(var)
            val arrType = getArrayType(actual_ty(tenv, varType, pos), pos)
          in
            (
              checkInt(tenv, trexp(exp), pos);
              {exp = (), ty = actual_ty(tenv, arrType, pos)}
            )
          end

        | trvar (A.FieldVar(var, symbol, pos)) =
            let
              val {exp = _, ty = varType} = trvar(var)
            in
              case actual_ty(tenv, varType, pos) of
                T.RECORD (fieldList, _) => 
                  let
                    val result = List.find (fn (s, _) => s = symbol) fieldList
                  in
                    case result of
                      SOME (s, ty) => {exp = (), ty = ty}
                      | NONE => (error pos ("no such field in record"); {exp = (), ty = T.UNIT})
                  end
              | _ => (error pos ("Should be record."); {exp = (), ty = T.UNIT})
            end

      in
        trexp exp
      end

    and transDecs (venv, tenv, []) = {venv = venv, tenv = tenv}
      | transDecs(venv, tenv, decs) =
        let
          fun trdec (A.VarDec{name, escape, typ = NONE, init, pos}, {venv, tenv}) =
            let 
              val {exp, ty} = transExp(venv, tenv, init)
            in 
              (assertNotNil (ty, pos);
               {tenv = tenv, venv = S.enter(venv, name, E.VarEntry{ty = ty})})
            end

            | trdec (A.VarDec{name, escape, typ = SOME(decTy, decTyPos), init, pos}, {venv, tenv}) =
                let 
                  val {exp, ty} = transExp(venv, tenv, init)
                  val decType = getType(tenv, decTy, pos)
                in
                  if isSameType(tenv, ty, decType, pos) then 
                      {tenv = tenv,venv = S.enter(venv, name, E.VarEntry{ty = ty})} 
                  else 
                      (
                        error pos ("Type wrong. Declared as " ^ S.name decTy); 
                        {tenv = tenv,venv = venv}
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
            | trdec (A.TypeDec[], {venv, tenv}) = (bugErr 0 "Type declaration list shouldn't be empty"; {venv = venv, tenv = tenv})
            | trdec (A.TypeDec(tydecs), {venv, tenv = globalTenv}) = (* tydecs: {name: symbol, ty: ty, pos: pos} list *)
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
                  {venv = venv, tenv = tenv''}
                end

            | trdec (A.FunctionDec[], {venv, tenv}) = (bugErr 0 "Function declaration list shouldn't be empty"; {venv = venv, tenv = tenv})
            | trdec (A.FunctionDec(fundecs), {venv, tenv}) =
              let
                val set = ref StringSet.empty
                fun addSymbolAndCheck (set, name, pos) =
                    if StringSet.member(set, S.name name)
                    then (error pos ("Duplicated type name in mutaul recursion: " ^ S.name name); set)
                    else StringSet.add(set, S.name name)
                fun transparam{name, escape, typ, pos} =
                    {name = name,ty = getType(tenv, typ, pos)}

                fun addSig({name, params, body, pos, result}, venv) =
                    let
                      val result_ty = case result of
                        SOME(rt, rtPos) => getType(tenv, rt, pos)
                        | NONE => T.UNIT
                      val params' = map transparam params
                      val _ = set := addSymbolAndCheck(!set, name, pos)
                    in
                      S.enter(venv,name, E.FunEntry{formals = map #ty params', result = result_ty})
                    end
                val venv' = foldl addSig venv fundecs

                fun checkBody({name, params, body, pos, result}, venv) =
                    let
                      val result_ty = case result of
                        SOME(rt, rtPos) => getType(tenv, rt, pos)
                        | NONE => T.UNIT
                      val params' = map transparam params
                      fun enterparam ({name, ty}, venv) =
                        S.enter(venv,name, E.VarEntry{(*access=(),*)ty=ty})
                      val venv'' = foldl enterparam venv' params'
                      val {exp, ty=bodyTy} = transExp(venv'', tenv, body)
                      val _ = if isSameType(tenv, bodyTy, result_ty, pos) then ()
                              else error pos "function body and return type mismatch"
                   in
                       venv
                   end
                val venv'' = foldl checkBody venv fundecs
              in
                  {venv = venv', tenv = tenv}
              end
        in
          foldl trdec {venv = venv, tenv = tenv} decs 
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

    fun transProg(exp: A.exp) : unit =
      (
        transExp(E.base_venv, E.base_tenv, exp); 
        ()
      );
end

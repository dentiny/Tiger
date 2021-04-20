structure A = Absyn
structure S = Symbol

structure FindEscape : sig val findEscape: A.exp -> unit
		       end =

struct
  type depth = int
  type escEnv = (depth * bool ref) S.table
  fun traverseVar (env: escEnv, d: depth, s: A.var) : unit =
    let
      fun trvar (A.SimpleVar(id, pos)) =
      (
          case S.look (env, id) of
          NONE => ()
        | SOME(decDepth, escRef) => if (d > decDepth) then escRef := true else ()
      )
        | trvar (A.SubscriptVar(var, exp, pos)) = (trvar(var); traverseExp(env, d, exp))
        | trvar (A.FieldVar(var, symbol, pos)) = trvar(var)
    in
      trvar(s)
    end

  and

  traverseExp (env: escEnv, d: depth, s: A.exp) : unit =
    let
      fun trexp (A.NilExp) = ()
        | trexp (A.IntExp(_)) = ()
        | trexp (A.StringExp(_)) = ()
        | trexp (A.VarExp(v)) = traverseVar(env, d, v)
        | trexp (A.LetExp{decs, body, pos}) = traverseExp(traverseDecs(env, d, decs), d, body)
        | trexp (A.OpExp{left, oper, right, pos}) = (trexp(left); trexp(right))
        | trexp (A.AssignExp{var, exp, pos}) = (traverseVar(env, d, var); trexp(exp))
        | trexp (A.IfExp{test, then', else' = NONE, pos}) = (trexp(test); trexp(then'))
        | trexp (A.IfExp{test, then', else' = SOME(elseVal), pos}) = (trexp(test); trexp(then'); trexp(elseVal))
        | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
          (
            traverseExp(S.enter(env, var, (d, escape)), d, body);
            trexp(lo);
            trexp(hi)
          )
        | trexp (A.WhileExp{test, body, pos}) = (trexp(test); trexp(body))
        | trexp (A.BreakExp(pos)) = ()
        | trexp (A.SeqExp(expSeq)) = app (fn (exp, _) => trexp(exp)) expSeq
        | trexp (A.CallExp{func, args, pos}) = app trexp args
        | trexp (A.RecordExp{fields, typ, pos}) = app (fn (_, exp, _) => trexp(exp)) fields
        | trexp (A.ArrayExp{typ, size, init, pos}) = (trexp(size); trexp(init))
    in
      trexp(s)
    end

  and

  traverseDecs (env, d, s: A.dec list) : escEnv =
    let
      fun applyDec (A.VarDec{name, typ, init, escape, pos}, env) = S.enter(env, name, (d, escape))
        | applyDec (A.TypeDec(_), env) = env
        | applyDec (A.FunctionDec(fundecs), env) =
          (*
            1. Add parameters into env.
            2. Escape analysis in the scope of function.
            3. Funtion declaration gets new depth, function call generates new frame.
          *)
          let
            fun updateFunEnv({name, params, result, body, pos}) =
              let
                val fundecEnv = foldl (fn ({name, escape, typ, pos}, env) => S.enter(env, name, (d + 1, escape))) env params
              in
                traverseExp(fundecEnv, d + 1, body)
              end
          in
            (app updateFunEnv fundecs; env)
          end
    in
      foldl applyDec env s
    end

  fun findEscape (prog: A.exp) : unit = traverseExp(S.empty, 0, prog)

end

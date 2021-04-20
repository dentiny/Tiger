(* Interface between Semant and Translate, to genrate IR tree structure. *)

signature TRANSLATE =
sig
    (* type level *)
    type access (* Different from Frame.access *)
    type exp
    type frag
    datatype level =
        BaseLevel
    | Level of {parent: level, frame: MipsFrame.frame, levelRef: unit ref}
   
    val outermost : level
    val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
    val formals : level -> access list
    val allocLocal : level -> bool -> access
    
    val procEntryExit : {level: level, body: exp} -> unit
    val getResult : unit -> frag list
    val transResExp : exp -> Tree.stm (* for printtree.sml as input *)

    (* Interface reserved for semant. *)
    val transNil : unit -> exp
    val transInt : int -> exp
    val transBool : bool -> exp
    val transStr : string -> exp
    val transBinop : (Absyn.oper * exp * exp) -> exp
    val transRelop : (Absyn.oper * exp * exp * Types.ty) -> exp
    val transAssign : (exp * exp) -> exp
    val transIfThen : (exp * exp) -> exp
    val transIfThenElse : (exp * exp * exp) -> exp
    val transFor : (exp * exp * exp * Temp.label) -> exp
    val transWhile : (exp * exp * Temp.label) -> exp
    val transBreak : Temp.label option -> exp
    val transMkArray : (exp * exp) -> exp
    val transMkRecord : exp list -> exp
    val transLet : exp list * exp -> exp
    val transVarDec : (access * exp) -> exp
    val transCall : (level * level * Temp.label * exp list) -> exp
    val transSeq : exp list -> exp
    val transSimpleVar : access * level -> exp
    val transSubscript : exp * exp -> exp
    val transField : exp * int -> exp
end
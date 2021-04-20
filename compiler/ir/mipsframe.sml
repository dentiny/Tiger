structure MipsFrame : FRAME =
struct
  (* Formals and locals may be in the frame or in registers. *)
  datatype access = InFrame of int (* InFrame(X) indicates a memory location at offset X from the frame pointer *)
		              | InReg of Temp.temp (* InReg(t64) indicates that it will be held in register t64 *)

  (*The type frame holds information about formal parameters and 
  	local variables allocated in this frame.*)
  type frame = {name: Temp.label, formals: access list, locals: int ref}
  
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  (* Registers *)
  val wordSize = 4
  val FP = Temp.newtemp()
  val RV = Temp.newtemp()

  fun exp (InReg(k))(_) = Tree.TEMP(k)
    | exp (InFrame(k))(fp) = Tree.MEM(Tree.BINOP(Tree.PLUS, fp, Tree.CONST(k)))

  fun newFrame {name = f, formals = l} =
  	let
  		val formalOffset = ref 0
  		(*escape true: inner function may use the variable. Put it in the frame.*)
  		(*otherwise put it in a register*)
  		fun allocFormal true = (formalOffset := (!formalOffset) + wordSize; InFrame (!formalOffset))
  			| allocFormal false = InReg(Temp.newtemp())
  	in
  		{name = f, formals = map allocFormal l, locals = ref ~1}
  	end
(*TODO: FP*)
  fun allocLocal {name, formals, locals} true = (locals := !locals + 1; InFrame (!locals * ~wordSize))
  	| allocLocal {name, formals, locals} false = InReg(Temp.newtemp())

  fun name 	  {name, formals, locals} = name
  fun formals {name, formals, locals} = formals
  
  fun externalCall(func, args) = Tree.CALL(Tree.NAME(Temp.namedlabel(func)), args)

  fun procEntryExit1(frame,body) = body
end
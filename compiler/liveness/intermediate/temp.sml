structure Temp : TEMP =
struct
    type temp = int
    val labelCount = ref 0
    val temps = ref 100
    val labelReset = ref 0
    val tempReset = ref 100
    val compare = Int.compare
    structure Table = IntMapTable(type key = int
                  fun getInt n = n)
    fun start() =
        let val () = labelReset := !labelCount
            val () = tempReset := !temps
        in
            ()
        end
                        
    fun reset () = 
	let val () = temps := !tempReset
	    val () = labelCount := !labelReset
	in
	    ()
	end

    fun newtemp() = 
	let val t  = !temps 
	    val () = temps := t+1
	in 
	    t
	end
    fun makestring t = "t" ^ Int.toString t
		       
    type label = Symbol.symbol
    
    structure TempOrd =
    struct 
      type ord_key = temp
      val compare = Int.compare
    end

    structure Set = SplaySetFn(TempOrd)
    structure Map = SplayMapFn(TempOrd)
			 
    fun newlabel() = 
	let val x  = !labelCount
	    val () = labelCount := x +1
	in
	    (*Symbol.symbol name*)
        Symbol.symbol(Format.format "L%d" [Format.INT(!labelCount)])
	end
    val namedlabel = Symbol.symbol


end

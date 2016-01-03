signature FRAME =
sig

  type frame (* describe a stack frame *)
  type access (* describe a formal arg or local var, in register or in frame *)
  type register (* describe a concrete register *)

  val FP: Temp.temp
  val SP: Temp.temp
  val RV: Temp.temp
  val EAX: Temp.temp
  val EBX: Temp.temp
  val ECX: Temp.temp
  val EDX: Temp.temp
  val ESI: Temp.temp
  val EDI: Temp.temp
  
  val XMM0: Temp.temp
  val XMM1: Temp.temp
  val XMM2: Temp.temp
  val XMM3: Temp.temp
  val XMM4: Temp.temp
  val XMM5: Temp.temp
  val XMM6: Temp.temp
  val XMM7: Temp.temp

  val registers: register list
  val wordSize: int

  val calldefs : Temp.temp list
  val calleesaves : Temp.temp list
  val callersaves : Temp.temp list

  val newFrame: {name: Temp.label, formals: int} -> frame
  val name: frame -> Temp.label
  val accessOfFormal: int -> bool -> access
  val accessOfTemp: int -> access
  val allocLocal: frame -> bool -> access
  val allocMember: frame -> access
  val allocVtableEntry: int -> bool -> access
  val allocGlobal: Symbol.symbol -> bool -> access
  val memberInClass: Tree.exp -> access -> Tree.exp
  
  val number2formal: int -> Tree.exp
  val exp: access -> Tree.exp -> Tree.exp
  val string: Temp.label * string -> string
  val number: Temp.label * string -> string
  val global: Symbol.symbol -> string
  val table: Temp.label * (Temp.label list) -> string
  val externalCall: string * Tree.exp list -> Tree.exp

  val entryExit1: frame * Tree.stm -> Tree.stm
  val entryExit2: frame * Assem.instr list -> Assem.instr list
  val entryExit3: frame * Assem.instr list -> { prolog: string
                                                  , body: Assem.instr list
                                                  , epilog: string}

  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string
                | NUMBER of Temp.label * string
				| GLOBAL of Symbol.symbol * bool
				| TABLE of Temp.label * (Temp.label list)
				
  val emit: TextIO.outstream -> (TextIO.outstream * frag list * frag -> frag list) -> string -> frag list -> unit
  val toReg: register Temp.Table.table -> Temp.temp -> register
  val forceSize: Tree.size -> Temp.temp -> unit
  val size: Temp.temp -> Tree.size option
				
  (* Printing *)
  val tempMap: register Temp.Table.table
  val asStringReg: Temp.temp -> string
  val asStringFrame: frame -> string
  val asStringAccess: access -> string
  val printFrame: TextIO.outstream * frame -> unit
  val printAccess: TextIO.outstream * access -> unit

end (* FRAME *)

signature REG_ALLOC =
sig
	structure Frame : FRAME
	type allocation = Frame.register Temp.Table.table
	val alloc : Assem.instr list * Frame.frame * IntBinarySet.set Temp.Table.table -> Assem.instr list * allocation
end
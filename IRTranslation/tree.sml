structure Tree: TREE =
struct

    type label = Temp.label

    datatype stm = SEQ of stm * stm
                 | LABEL of label
                 | JUMP of exp * label list
                 | INTCJUMP of relop * exp * exp * label * label
				 | FLOATCJUMP of relop * exp * exp * label * label
				 | MOVE of exp * exp
                 | EXP of exp

	and exp = INTBINOP of binop * exp * exp
			| FLOATBINOP of binop * exp * exp
			| MEM of exp * size
			| TEMP of Temp.temp
			| ESEQ of stm * exp
			| NAME of label
			| CONST of constdata
			| CALL of exp * exp list

	and size = BYTE
			 | WORD
			 | DWORD
			
	and constdata = INT of int
				  | FLOAT of real
				  | DEFINE of string

	and binop = PLUS | MINUS | MUL | DIV
			  | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR
			  | BEQ | BNEQ | BLT | BGT | BLE | BGE
			  
   and relop = REQ | RNEQ | RLT | RGT | RLE | RGE

fun notRel REQ = RNEQ
  | notRel RNEQ = REQ
  | notRel RLT = RGE
  | notRel RGT = RLE
  | notRel RLE = RGT
  | notRel RGE = RLT
  
end (* Tree *)
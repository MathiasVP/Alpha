structure Types : TYPES =
struct
	datatype ty = FUNCTION of ty list * ty
				| ARRAY of ty
				| INTERFACE of { name: Symbol.symbol
							   , extends: ty option}
				| CLASS of { name: Symbol.symbol
						   , extends: ty option
						   , implements: ty list}
				| INT
				| CHAR
				| STRING
				| FLOAT
				| VOID
				| BOOL
				| ERROR
end (* Types *)


signature TYPES =
sig

	datatype ty = FUNCTION of ty list * ty
				| ARRAY of ty
				| INT
				| CHAR
				| STRING
				| FLOAT
				| VOID
				| BOOL
				| ERROR
				| INTERFACE of { name: Symbol.symbol
							   , extends: ty option}
				| CLASS of { name: Symbol.symbol
						   , extends: ty option
						   , implements: ty list}
end


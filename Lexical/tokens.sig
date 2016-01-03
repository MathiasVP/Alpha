signature Alpha_TOKENS =
sig

type token

val VAR:			int * int -> token
val FUN:			int * int -> token
val BREAK:			int * int -> token
val RETURN:			int * int -> token
val ARRAY:			int * int -> token
val FOR:			int * int -> token
val NEW:			int * int -> token
val WHILE:			int * int -> token
val ELSE:			int * int -> token
val IF:				int * int -> token
val INTERFACE:		int * int -> token
val CLASS:			int * int -> token
val IMPLEMENTS:		int * int -> token
val EXTENDS:		int * int -> token
val PUBLIC:			int * int -> token
val PROTECTED:		int * int -> token
val PRIVATE:		int * int -> token
val ASSIGN:			int * int -> token
val PLUSASSIGN:		int * int -> token
val MINUSASSIGN:	int * int -> token
val TIMESASSIGN:	int * int -> token
val DIVIDEASSIGN:	int * int -> token
val OR:				int * int -> token
val AND:			int * int -> token
val GE:				int * int -> token
val GT:				int * int -> token
val LE:				int * int -> token
val LT:				int * int -> token
val NEQ:			int * int -> token
val EQ:				int * int -> token
val DIVIDE:			int * int -> token
val TIMES:			int * int -> token
val MINUS:			int * int -> token
val PLUSPLUS:		int * int -> token
val MINUSMINUS:		int * int -> token
val PLUS:			int * int -> token
val DOT:			int * int -> token
val RBRACE:			int * int -> token
val LBRACE:			int * int -> token
val RPAREN:			int * int -> token
val LPAREN:			int * int -> token
val LBRACK:			int * int -> token
val RBRACK:			int * int -> token
val SEMICOLON:		int * int -> token
val COMMA:      	int * int -> token
val BANG:			int * int -> token
val ARROW:      	int * int -> token
val STRING:			string *  int * int -> token
val CHAR:			string *  int * int -> token
val INT:			int *	  int * int -> token
val BOOL:			bool *	  int * int -> token
val FLOAT:			real *	  int * int -> token
val ID:				string *  int * int -> token
val EOF:			int * int -> token

end (* Alpha_TOKENS *)

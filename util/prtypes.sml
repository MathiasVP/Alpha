structure PrintTypes: PRINTTYPES =
struct

structure T = Types

fun formatList f sep [] = ""
  | formatList f sep lst =
	let
		val s = List.foldl (fn(elem, acum) => acum ^ sep ^ f elem) "" lst;
		val n = String.size sep;
	in
		String.substring (s, n, String.size s - n)
	end;

fun asString T.INT = "int"
  | asString T.STRING = "string"
  | asString T.FLOAT = "float"
  | asString T.VOID = "void"
  | asString T.BOOL = "bool"
  | asString T.ERROR = "error"
  | asString (T.FUNCTION (tys, ty)) =
	"fun(" ^ formatList asString ", " tys ^ ") -> " ^ asString ty
  | asString (T.ARRAY ty) =
	"[" ^ asString ty ^ "]"
  | asString T.CHAR = "char"
  | asString (T.INTERFACE {name, extends, ...}) = Symbol.name name
  | asString (T.CLASS {name, implements, extends}) = Symbol.name name

end (* PrintTypes *)


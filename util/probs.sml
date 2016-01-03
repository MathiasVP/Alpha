structure PrintOperators: PRINTOPERATORS =
struct

structure A = Absyn;

fun asString A.PlusOp = "+"
  | asString A.MinusOp = "-"
  | asString A.TimesOp = "*"
  | asString A.DivideOp = "/"
  | asString A.AndOp = "&&"
  | asString A.OrOp = "||"
  | asString A.EqOp = "=="
  | asString A.NeqOp = "!="
  | asString A.LtOp = "<"
  | asString A.LeOp = "<="
  | asString A.GtOp = ">"
  | asString A.GeOp = ">="
  | asString A.BangOp = "!"
  | asString A.UminusOp = "-"

end (* PrintOperators *)
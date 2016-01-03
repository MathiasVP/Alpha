signature TEMP = 
sig
  (* p140 *)
  eqtype temp
  val newtemp : unit -> temp
  structure Table : TABLE sharing type Table.key = temp
  structure Set : ORD_SET sharing type Set.Key.ord_key = temp
  val makestring: temp -> string
  type label = Symbol.symbol
  val newLabel : string -> label (* string: hint for human reader *)
  val namedLabel : string -> label
  val topLabel: label
end


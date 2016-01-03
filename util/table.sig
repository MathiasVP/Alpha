signature TABLE =
sig
   type key
   type 'a table
   val empty      : 'a table
   val enter      : 'a table * key * 'a -> 'a table
   val look       : 'a table * key -> 'a option
   val collate	  : (('a * 'a) -> order) -> ('a table * 'a table) -> order
   val unionWith  : (('a * 'a) -> 'a) -> ('a table * 'a table) -> 'a table
   val map		  : ('a -> 'b) -> 'a table -> 'b table
   val foldli	  : ((key * 'a * 'b) -> 'b) -> 'b -> 'a table -> 'b
   val numItems   : 'a table -> int
   val fromList   : (key * 'a) list -> 'a table
   val entries : 'a table -> (key * 'a) list
end


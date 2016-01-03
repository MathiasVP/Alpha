signature WORK_LISTS = sig
	type id
	type item
	type lists
	structure Set : ORD_SET sharing type Set.Key.ord_key = item

	datatype collection = List of item list
						| Set of Set.set

	val asSet: lists -> id -> Set.set
	val asList: lists -> id -> item list
	val isMember: lists -> id -> item -> bool
	val isMember': lists -> item -> id -> bool
	val isEmpty: lists -> id -> bool
	val move: lists -> id -> id -> item -> lists
	val move': lists -> item -> id -> id -> lists
	val newId: string -> id
	val newLists: (id * collection) list -> lists

	val debug: (item -> string) * lists -> unit
end
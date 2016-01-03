functor WorkLists (structure Set : ORD_SET) : WORK_LISTS =
	struct
		type id = Symbol.symbol
		type item = Set.item
		structure Set = Set

		datatype collection = List of item list
							| Set of Set.set

		type lists = collection Symbol.table

		fun eq a b = Set.Key.compare (a, b) = General.EQUAL

		fun get (lists, id) : collection =
			case Symbol.look (lists, id) of
				SOME collection => collection
			  | NONE => raise Fail ("Lists doesn't contain " ^ (Symbol.name id))

		fun asSet lists id =
			case get (lists, id) of
				List list => Set.addList (Set.empty, list)
			  | Set set => set

		fun asList lists id =
			case get (lists, id) of
				List list => list
			  | Set set => Set.listItems set

		fun isMember lists id item =
			case get (lists, id) of
				List list => List.exists (eq item) list
			  | Set set => Set.member (set, item)

		fun isMember' lists item id =
			case get (lists, id) of
				List list => List.exists (eq item) list
			  | Set set => Set.member (set, item)

		fun isEmpty lists id =
			case get (lists, id) of
				List list => List.null list
			  | Set set => Set.isEmpty set

	fun move lists srcId dstId item =
		let
			fun removeList (_, []) = raise Fail "item was not present (in list)"
			  | removeList (item, item' :: rest) =
					if eq item item' then rest
					else item' :: (removeList (item, rest))

			fun removeSet (item, set) =
				if Set.member (set, item) then
					Set.delete (set, item)
				else
					raise Fail "item was not present (in set)"

			fun remove (item, List list) = List (removeList (item, list))
			  | remove (item, Set set) = Set (removeSet (item, set))

			val insertList = op::
			fun insertSet (item, set) = Set.add (set, item)

			fun insert (item, List list) = List (insertList (item, list))
			  | insert (item, Set set) = Set (insertSet (item, set))

			val src = get (lists, srcId)
			val src' = remove (item, src)
			val dst = get (lists, dstId)
			val dst' = insert (item, dst)
		in
			foldl (fn ((k, a), table) => Symbol.enter (table, k, a)) lists [(srcId, src'), (dstId, dst')]
		end

	fun move' lists item srcId dstId = move lists srcId dstId item

	val newId = Symbol.symbol

	fun newLists initials =
		foldr (fn ((id, initial), sets) => Symbol.enter (sets, id, initial))
			Symbol.empty initials

	fun debug (toStr, wls) =
		let
			fun listToString list = String.concatWith ", " (map toStr list)
		in
			List.app (fn key =>
			let
				val _ = print (Symbol.name key ^ ": [");
				val s = case Symbol.look (wls, key) of
						SOME (List list) => listToString list
					  | SOME (Set set) => listToString (Set.listItems set)
					  | NONE => raise Fail "Working list not found"
			in
				print (s ^ "]\n")
			end) (map #1 (Symbol.entries wls))
	end
end
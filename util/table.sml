functor IntMapTable (type key
			val getInt: key -> int
			val getKey: int -> key): TABLE =
struct

type key = key
type 'a table = 'a IntBinaryMap.map
val empty = IntBinaryMap.empty
fun enter (t, k, a) = IntBinaryMap.insert (t, getInt k, a)
fun look (t, k) = IntBinaryMap.find (t, getInt k)
fun collate cmp (t1, t2) = IntBinaryMap.collate cmp (t1, t2)
fun unionWith f (ma, ma2) = IntBinaryMap.unionWith f (ma, ma2)
fun map f ma = IntBinaryMap.map f ma
fun foldli f a ma = IntBinaryMap.foldli (fn (k, a', b') => f (getKey k, a', b')) a ma
val numItems = IntBinaryMap.numItems
fun fromList kas =
    let
        fun fromList1 [] t = t
          | fromList1 ((k, a)::kas) t = enter (fromList1 kas t, k, a)
    in
        fromList1 kas empty
    end
fun entries (t) = List.map (fn (i, v) => (getKey i, v))
	(IntBinaryMap.listItemsi (t : 'a table))

end (* IntMapTable *)


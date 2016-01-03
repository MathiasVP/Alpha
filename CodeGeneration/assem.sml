structure Assem =
struct

type reg = string
type temp = Temp.temp
type label = Temp.label

datatype instr = OPER of  { assem: string
                          , dst: temp list
                          , src: temp list
                          , jump: label list option
                          , doc: string}
               | LABEL of { assem: string
                          , lab: Temp.label
                          , doc: string}
               | MOVE of  { assem: string
                          , dst: temp
                          , src: temp
                          , doc: string}

fun addDoc assem doc =
    (if size doc = 0 then assem else
     let
         fun padded vsz n s =
             if vsz < n-10 then padded (vsz+10) n (s ^ "          ")
             else if vsz < n then padded (vsz+1) n (s ^ " ")
             else s
         fun visualSize s =
             let
                 val chars = explode s
                 fun vsz [] sz = sz
                   | vsz (#"\n"::cs) sz = vsz cs 0
                   | vsz (#"\t"::cs) sz = vsz cs (((sz div 8) + 1) * 8)
                   | vsz (c::cs) sz = vsz cs (sz+1)
             in
                 vsz chars 0
             end
         val assem' = padded (visualSize assem) 49 assem ^ " "
         val sep = if String.isSubstring ";" assem then "," else ";"
         val assem'' = assem' ^ sep ^ " "
     in
         assem'' ^ doc
     end) ^
    "\n"

fun format saytemp =
    let
        fun speak (assem, dst, src, jump, doc) =
            let
                val saylab = Symbol.name
                fun f (#"`":: #"s":: i::rest) =
                    (explode (saytemp (List.nth(src,ord i - ord #"0"))) @ f rest)
                  | f ( #"`":: #"d":: i:: rest) =
                    (explode (saytemp (List.nth(dst,ord i - ord #"0"))) @ f rest)
                  | f ( #"`":: #"j":: i:: rest) =
                    (explode (saylab (List.nth(jump,ord i - ord #"0"))) @ f rest)
                  | f ( #"`":: #"`":: rest) =
                    #"`" :: f rest
                  | f ( #"`":: _ :: rest) =
                    ErrorMsg.impossible "bad Assem format"
                  | f (c :: rest) =
                    (c :: f rest)
                  | f nil =
                    nil
            in
                addDoc (implode (f (explode assem))) doc
            end
    in
        fn OPER {assem, dst, src, jump=NONE, doc} =>
           speak (assem, dst, src, nil, doc)
         | OPER {assem, dst, src, jump=SOME j, doc} =>
           speak (assem, dst, src, j, doc)
         | LABEL {assem, doc, ...} =>
           addDoc assem doc
         | MOVE {assem, dst, src, doc} => 
			 if saytemp dst <> saytemp src then
				speak (assem, [dst], [src], nil, doc) else ""
    end

end (* Assem *)


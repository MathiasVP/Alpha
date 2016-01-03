structure Env :> ENV = 
struct

structure S = Symbol
structure Ty = Types
structure Tm = Temp
structure Tr = Translate

datatype visibility = Public
				 | Protected of Ty.ty
				 | Private of Ty.ty

type VarT = { access: Translate.access
			, level: Tr.level
			, ty: Ty.ty
			, vis: visibility
			, gcAccess: Translate.access option }

type FunT = { formals: Ty.ty list
			, result: Ty.ty
			, label: Tm.label
			, level: Tr.level
			, access: Translate.access
			, vis: visibility }
				 
datatype enventry = VarEntry of VarT
                  | FunEntry of FunT
				  | ClassEntry of { methods: (S.symbol * FunT) list,
									tyOffsets: (Ty.ty * int) list,
									constructors: enventry list,
									variables: (S.symbol * enventry) list,
									vtableLabel: Tm.label }
				  | InterfaceEntry of { entries: (S.symbol * FunT) list }

val initLevel = Tr.newLevel { parent = Tr.outermost
                            , name = Tm.topLabel
                            , formals = 0}

fun enter ((symbol, entry), env) = S.enter (env, symbol, entry)

val baseTenv =
    foldl enter S.empty 
          [ (S.symbol "int", Ty.INT)
          , (S.symbol "string", Ty.STRING)
		  , (S.symbol "float", Ty.FLOAT)
		  , (S.symbol "void", Ty.VOID)
		  , (S.symbol "bool", Ty.BOOL)
		  , (S.symbol "char", Ty.CHAR) ]


local
	fun makeFun (name, argsTy, resTy) =
		let val sym = S.symbol name
		in (sym, FunEntry {formals = [Ty.STRING],
						   result = Ty.VOID,
						   label = Tm.namedLabel name,
						   level = initLevel,
						   access = Tr.allocGlobal initLevel sym false,
						   vis = Public })
		end
in		  
val baseVenv = foldl enter S.empty [
	makeFun ("print", [Ty.STRING], Ty.VOID)
]
end

end (* Env *)


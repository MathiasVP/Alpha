signature ENV =
sig
	datatype visibility = Public
						| Protected of Types.ty
						| Private of Types.ty

	type VarT = { access: Translate.access
				, level: Translate.level
				, ty: Types.ty
				, vis: visibility
				, gcAccess : Translate.access option }
									
	type FunT = { formals: Types.ty list
				, result: Types.ty
				, label: Temp.label
				, level: Translate.level
				, access: Translate.access
				, vis: visibility }
						
	datatype enventry = VarEntry of VarT
					  | FunEntry of FunT
					  | ClassEntry of { methods: (Symbol.symbol * FunT) list,
										tyOffsets: (Types.ty * int) list,
										constructors: enventry list,
										variables: (Symbol.symbol * enventry) list,
										vtableLabel: Temp.label }
					  | InterfaceEntry of { entries: (Symbol.symbol * FunT) list }

	val initLevel: Translate.level
	val baseTenv: Types.ty Symbol.table
	val baseVenv: enventry Symbol.table
end

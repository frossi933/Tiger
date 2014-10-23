structure tigertips =
struct

type unique = unit ref
datatype Tipo = TUnit
	| TNil
	| TInt
	| TROInt
	| TString
	| TArray of Tipo * unique
	| TRecord of (string * Tipo * int) list * unique
	| TTipo of string * Tipo option ref



fun printTipo TUnit = "tunit"
	| printTipo TNil = "tnil"	
	| printTipo TInt = "tint"
	| printTipo TROInt = "troint"
	| printTipo TString = "tstring"
	| printTipo (TArray (t, _)) = "array ("^printTipo t^")"
	| printTipo (TRecord (fs, _)) = List.foldl (fn ((n, t, p),res) => "("^n^"::"^printTipo t^"); "^res) "" fs
	| printTipo (TTipo (s, r)) = (case !r of
				NONE => "ttipo "^s^" none"
				| SOME t => "ttipo "^s^" ("^printTipo t^" )")

end

structure tigertips =
struct

(* Since every record type expression creates a new and different record
   type we have a "unique" value to distinguish it *)
type unique = unit ref

datatype Tipo = TUnit
	| TNil
	| TInt
	| TROInt
	| TString
	| TArray of Tipo * unique
	| TRecord of (string * Tipo * int) list * unique
	| TFunc of Tipo list * Tipo
	(* When processing mutually recursive types, we will need a place-holder
	   for types whose name we know but whose definition we have not yet seen *)
	| TTipo of string * Tipo option ref

end

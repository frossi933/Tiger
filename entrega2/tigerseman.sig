signature tigerseman =
sig

  type tenv = (string, tigertips.Tipo) tigertab.Tabla
	val transProg: tigerabs.exp -> unit

end

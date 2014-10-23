signature topsort =
sig
    
    exception Ciclo
    val fijaTipos : {name: tigerabs.symbol, ty: tigerabs.ty} list -> tigerseman.tenv -> tigerseman.tenv

end

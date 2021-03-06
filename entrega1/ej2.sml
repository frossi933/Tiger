structure ej2 =
struct

open tigerabs

fun cantprints (CallExp ({func = "print", args},_)) = if (List.filter (fn (StringExp _) => true | _ => false) args)=[] 
                                                      then 1 + (List.foldr op+ 0 (List.map cantprints args)) 
                                                      else (List.foldr op+ 0 (List.map cantprints args))
|   cantprints (OpExp ({left, right, ...},_))      = cantprints left + cantprints right
|   cantprints (RecordExp ({fields, ...}, _))      = List.foldr op+ 0 (List.map (fn (_, e) =>   cantprints e) fields)
|   cantprints (SeqExp (expl, _))                  = (List.foldr op+ 0 (List.map cantprints expl)) 
|   cantprints (AssignExp ({exp, ...}, _))         = cantprints exp
|   cantprints (IfExp ({test, then', else'}, _))   = (case else' of
                                                           NONE   => cantprints test + cantprints then'
                                                           | SOME e => cantprints test + cantprints then' + cantprints e)
|   cantprints (ForExp ({lo, hi, body, ... }, _))  = cantprints lo + cantprints hi + cantprints body
|   cantprints (WhileExp ({test, body}, _))        = cantprints test + cantprints body
|   cantprints (LetExp ({body, ... }, _))          = cantprints body
|   cantprints (ArrayExp ({size, init, ... }, _))  = cantprints size + cantprints init
|   cantprints _                                   = 0

end

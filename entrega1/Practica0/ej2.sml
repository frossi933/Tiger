structure Ej2 =
struct

open tigerabs

fun cantprints (CallExp ({func = "print",args},_))        = 1 + (List.foldr op+ 0 (List.map cantprints args))
|   cantprints (OpExp ({left=l, right=r, ...},_))                  = cantprints l + cantprints r
|   cantprints (RecordExp ({fields=lf, ...}, _))                   = List.foldr op+ 0 (List.map (fn (_, e) =>   cantprints e) lf)
|   cantprints (SeqExp (expl, _))                                  = (List.foldr op+ 0 (List.map cantprints expl)) 
|   cantprints (AssignExp ({exp=e, ...}, _))                       = cantprints e
|   cantprints (IfExp ({test=etest, then'=ethen, else'=eelse}, _)) = (case eelse of
                                                                       NONE   => cantprints etest + cantprints ethen
                                                                     | SOME e => cantprints etest + cantprints ethen + cantprints e)
|   cantprints (ForExp ({lo=elo, hi=ehi, body=ebody, ... }, _))    = cantprints elo + cantprints ehi + cantprints ebody
|   cantprints (WhileExp ({test=etest, body=ebody}, _))            = cantprints etest + cantprints ebody
|   cantprints (LetExp ({body=ebody, ... }, _))                    = cantprints ebody
|   cantprints (ArrayExp ({size=esize, init=einit, ... }, 0))      = cantprints esize + cantprints einit
|   cantprints _                                                   = 0

end

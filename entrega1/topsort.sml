structure topsort :> topsort =
struct
(* Sort topolo'gico *)
open tigersres

exception Ciclo
fun topsort graph =
    let    fun cmp(x, y) = x=y
        fun mem(x, []) = false
        | mem(x, y::l) = cmp(x, y) orelse mem(x, l)
        fun nexts(a, []) = []
        | nexts(a, (x, y)::pairs) =
            if cmp(a, x) then y::nexts(a, pairs) else nexts(a, pairs)
        fun sort([], path, visited) = visited
        | sort(x::xs, path, visited) =
            if mem(x, path) then raise Fail "Ciclo"
            else sort(xs, path,
                    if mem(x, visited) then visited
                    else x::sort(nexts(x, graph), x::path, visited))
        val (starts, _) = ListPair.unzip graph
    in    sort(starts, [], []) end

fun genPares (lt:{name: symbol, ty: ty} list) = 
  let
      fun genP [] res = res
      | genP ({name, ty=NameTy s}::ts) res = genP ts ((s,name)::res)
      | genP ({name, ty=ArrayTy s}::ts) res = genP ts ((s,name)::res)
      | genP ({name, ty=RecordTy lf}::ts) res = genP ts res
  in
      genP lt []
  end


fun procesa [] _ _ env = env
| procesa (sorted as (h::t)) (decs:{name:symbol, ty:ty} list) recs env =
    let val (ps, ps') = List.partition (fn {ty=RecordTy lt, ... } => false
                                        | {ty=NameTy t, ...} => h=t
                                        | {ty=ArrayTy t, ...} => false) decs   (* los que necsitan a "h" *)
        val ttopt = (case List.find (fn x => h=(#name(x))) recs of
                        SOME {ty=ArrayTy _, name} => NONE
                        | SOME {ty=RecordTy _, ...} => NONE
                        | SOME _ => NONE
                        | NONE => (case tabBusca (h, env) of
                                    SOME t => SOME t
                                    | _ => raise Fail (h^" no existe!"))) 
        val env' = (case ttopt of
                    SOME tt => List.foldr (fn ({name, ty=NameTy _}, env') => tabInserta (name, tt, env')
					   (*| ({name, ty=ArrayTy _}, env') => tabInserta (name, TArray (tt, ref ()), env')*)
                                           | _ => raise Fail "error interno 666 :S") env ps
                    | _ => env)
    in procesa t ps' recs env'
    end

fun procRecords recs env =
    let fun buscaEnv env' t = (case tabBusca(t, env) of
                                SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                                | SOME t' => t'
                                | _ => (case tabBusca (t, env') of
                                        SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                                        | SOME t' => t'
                                        | _ => (case List.find (fn {name, ...} => name=t) recs of
                                               SOME {name, ...} => TTipo (name, ref NONE)
                                               | _ => raise Fail (t^" no existe!!!!"))))
        fun precs [] env' = env'
        | precs ({name, ty=RecordTy lf}::t) env' =
            let val lf' = List.foldl (fn ({name, typ=NameTy t, ...},l) => (name, buscaEnv env' t)::l
                                      | ({name, typ=ArrayTy t, ...},l) => (name, TArray (buscaEnv env' t, ref ()))::l
                                      | (_, l) => l) [] lf
                val (_, lf'') = List.foldl (fn ((x,y), (n,l)) => (n+1, (x, y, n)::l)) (0, []) lf'
                val env'' = tabInserta(name,TRecord (lf'', ref ()), env')
            in precs t env'' end
        | precs ({name, ty=ArrayTy ty}::t) env' = precs t (tabInserta (name, TArray (buscaEnv env' ty, ref ()), env'))
        | precs _ _ = raise Fail "error interno en precs"
    in precs recs (fromTab env) end

fun fijaNONE [] env = env
| fijaNONE ((name, TArray (TTipo (s, ref NONE), u))::t) env = (case tabBusca (s, env) of
                                                                SOME (r as (TRecord _)) => fijaNONE t (tabRInserta (name, TArray (TTipo (s, ref (SOME r)), u), env))
                                                                | _ => raise Fail "error interno en fijaNONE")
| fijaNONE ((name, TRecord (lf, u))::t) env = 
    let fun busNONE ((s, TTipo (t, ref NONE), n), l) =
                ((s, TTipo (t, ref (SOME ( tabSaca (t, env)))), n)::l)  
        | busNONE (d, l) = d::l
        val lf' = List.foldr busNONE [] lf
    in fijaNONE t (tabRInserta (name, TRecord (lf', u), env)) end
| fijaNONE (_::t) env = fijaNONE t env

fun fijaTipos (batch:{name: symbol, ty: ty} list) env = 
    let val pares = genPares batch
        val _ = (print ("pares:");List.map (fn (x,y) => print("("^x^","^y^") ")) pares;print("\n"))
        val recs = List.filter (fn {ty=NameTy _, ...} => false | _ => true) batch
        val orden = topsort pares
(*	val _  = (List.app (fn s => print (s^";")) orden; print "\n") *)
        val env' = procesa orden batch recs env
        val env'' = procRecords recs env'
        val env''' = fijaNONE (tabAList env'') env''
    in env''' end
end

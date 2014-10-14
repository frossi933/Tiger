structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt), ("string", TString)])

val levelPila: tigertrans.level tigerpila.Pila = tigerpila.nuevaPila1(tigertrans.outermost) 
fun pushLevel l = tigerpila.pushPila levelPila l
fun popLevel() = tigerpila.popPila levelPila 
fun topLevel() = tigerpila.topPila levelPila

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=topLevel(), label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=topLevel(), label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=topLevel(), label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=topLevel(), label="ord",
		formals=[TString], result=TInt, extern=true}),
	("chr", Func{level=topLevel(), label="chr",
		formals=[TInt], result=TString, extern=true}),
	("size", Func{level=topLevel(), label="size",
		formals=[TString], result=TInt, extern=true}),
	("substring", Func{level=topLevel(), label="substring",
		formals=[TString, TInt, TInt], result=TString, extern=true}),
	("concat", Func{level=topLevel(), label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=topLevel(), label="not",
		formals=[TInt], result=TInt, extern=true}),
	("exit", Func{level=topLevel(), label="exit",
		formals=[TInt], result=TUnit, extern=true})
	])

fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales TInt TROInt = true
  | tiposIguales TROInt TInt = true
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo (_, r)) b =
		let
			val a = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (1)"
		in
			tiposIguales a b
		end
  | tiposIguales a (TTipo (_, r)) =
		let
			val b = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (2)"
		in
			tiposIguales a b
		end
  | tiposIguales a b = (a=b)

(* Agregado *)
fun eqList _ [] [] = true
| eqList _ [] _ = false
| eqList _ _ [] = false
| eqList eq (x::xs) (y::ys) = if eq x y then eqList eq xs ys 
                                        else false 

fun transExp ((venv, tenv) : venv * tenv ): tigerabs.exp -> expty =
	let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
		| trexp(NilExp _)= {exp=nilExp(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt}
		| trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
		| trexp(CallExp({func, args}, nl)) = 
		    let
		        val tyf = (case tabBusca(func, venv) of
		                    SOME (Func {formals, result, ... }) => let 
		                                                             val tyArgs = List.map (fn arg => #ty (trexp arg)) args
		                                                           in  
		                                                             if eqList tiposIguales tyArgs formals then result
		                                                             else error("Argumentos incorrectos", nl)
       	   	                                                       end
		                    | SOME _                            => error(func^" no es una funcion", nl)
		                    | NONE                              => error(func^" no existe", nl))
		    in
		        {exp=nilExp(), ty = tyf}
		    end                                     (*COMPLETADO*)
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
					{exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=EqOp,right=expr} else binOpIntRelExp {left=expl,oper=EqOp,right=expr}, ty=TInt}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
					{exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=NeqOp,right=expr} else binOpIntRelExp {left=expl,oper=NeqOp,right=expr}, ty=TInt}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) = 
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
						| MinusOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
						| TimesOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
						| DivideOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
						| LtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
							{exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
							else error("Error de tipos", nl)
						| LeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then 
							{exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
							else error("Error de tipos", nl)
						| GtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
							{exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
							else error("Error de tipos", nl)
						| GeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
							{exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
							else error("Error de tipos", nl)
						| _ => raise Fail "No debería pasar! (3)"
				else error("Error de tipos", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case tipoReal t of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" no es de tipo record", nl))
					| NONE => error("Tipo inexistente ("^typ^")", nl)
				
				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar _ [] [] = []
				  | verificar _ (c::cs) [] = error("Faltan campos", nl)
				  | verificar _ [] (c::cs) = error("Sobran campos", nl)
				  | verificar n ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Error de campo", nl)
						else if tiposIguales ty t then (exp, n)::(verificar (n+1) cs ds)
							 else error("Error de tipo del campo "^s, nl)
				val lf = verificar 0 cs tfields
			in
				{exp=recordExp lf, ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	
			    val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=seqExp (exprs), ty=tipo } end
		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
		    let 
		        val aty = (case tabBusca(s, venv) of
		                        SOME (Var {ty=TROInt}) => error("Entero de solo lectura", nl)
		                        | SOME (Var {ty})      => if tiposIguales (#ty(trexp exp)) ty then TUnit
		                                                else error("Error de tipo de la expresion", nl)
		                        | SOME (Func _)        => error("Asignacion incorrecta", nl)
		                        | NONE                 => error("No existe variable", nl))
			in {exp=nilExp(), ty=aty} 
			end                                                        (* COMPLETADO *)
		| trexp(AssignExp({var, exp}, nl)) = 
		    let 
		        val tyVar = #ty (trvar (var,nl))
		        val tyExp = #ty (trexp exp)
			in if tiposIguales tyVar tyExp then {exp=nilExp(), ty=TUnit}
			                               else error("Asignacion incorrecta", nl) 
			end                                                       (* COMPLETADO *)
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if tipoReal tytest=TInt andalso tiposIguales tythen tyelse then
				{exp=if tipoReal tythen=TUnit then ifThenElseExpUnit {test=testexp,then'=thenexp,else'=elseexp} else ifThenElseExp {test=testexp,then'=thenexp,else'=elseexp}, ty=tythen}
				else error("Error de tipos en if" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let 
			    val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if tipoReal tytest=TInt andalso tythen=TUnit then
				{exp=ifThenExp{test=exptest, then'=expthen}, ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val ttest = trexp test
				val tbody = trexp body
			in
				if tipoReal (#ty ttest) = TInt andalso #ty tbody = TUnit then {exp=whileExp {test=(#exp ttest), body=(#exp tbody), lev=topLevel()}, ty=TUnit}
				else if tipoReal (#ty ttest) <> TInt then error("Error de tipo en la condición", nl)
				                                     else error("El cuerpo de un while no puede devolver un valor", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
		    let 
		        val tyLo = #ty (trexp lo)
		        val _ = if tyLo <> TInt andalso tyLo <> TROInt 
		                then error("Error en rango inferior de iteracion", nl) else ()
		        val tyHi = #ty (trexp hi)
		        val _ = if tyHi <> TInt andalso tyHi <> TROInt 
		                then error("Error en rango superior de iteracion", nl) else ()
		        val venv' = fromTab venv
		        val _ = tabInserta(var, Var {ty=TROInt}, venv')
		        val {ty=tyBody, ...} = transExp (venv', tenv) body
		    in 
		        if tyBody=TUnit then {exp=nilExp(), ty=TUnit}
	    	                    else error("El cuerpo debe devolver Unit", nl)
		    end                                                                (* COMPLETADO *)
		| trexp(LetExp({decs, body}, _)) =
			let
				fun aux (d, (v, t, exps1)) =
				let
					val (v', t', exps2) = trdec (v, t) d
				in
					(v', t', exps1@exps2)
				end
				val (venv', tenv', expdecs) = List.foldl aux (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in 
				{exp=seqExp(expdecs@[expbody]), ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=nilExp(), ty=TUnit}                                      (*COMPLETADO*)
		| trexp(ArrayExp({typ, size, init}, nl)) =
			let 
			    val sizTy = #ty (trexp size)
			    val _ = if sizTy <> TInt orelse sizTy <> TROInt 
			            then error("El tamaño del arreglo no es un numero", nl) else ()
			    val typTy = (case tabBusca (typ, tenv) of
			                    SOME t => t
			                    | NONE => error("No existe el tipo "^typ, nl))
			    val iniTy = #ty (trexp init)
			    val _ = if not (tiposIguales iniTy typTy) 
			            then error("No coincide el tipo del inicializador", nl) else ()
			in
			    {exp=nilExp(), ty=TUnit}
			end                                    (*COMPLETADO*) 
		and trvar(SimpleVar s, nl) =
		    (case tabBusca (s, venv) of
		        SOME (Var {ty}) => {exp=nilExp(), ty=ty}
		        | SOME _        => error(s^" no es una variable", nl)
		        | _             => error("No existe "^s, nl))        (*COMPLETADO*)
		| trvar(FieldVar(v, s), nl) =
		    let
		        val sTy   = (case trvar(v, nl) of
    		                    {ty=(TRecord (l,u)), ... } => (case List.find (fn (n, _, _) => n=s) l of
    		                                            SOME (n, t, i) => t
    		                                            | _            => error(s^" no es un campo del record", nl))
	    	                    | _       => error("La variable no es un record", nl))
		    in {exp=nilExp(), ty=sTy}
		    end                                               (* COMPLETADO *)
		| trvar(SubscriptVar(v, e), nl) =
		    let
		        val vTy = (case trvar(v, nl) of
		                        {ty=(TArray (t, u)), ...} => t
		                        | _           => error("La variable no es un arreglo", nl))
		        val {exp=eExp, ty=eTy} = trexp e 
		    in 
		        if tiposIguales eTy TInt then {exp=nilExp(), ty=vTy}
		                                 else error("el indice no es un numero", nl)
		    end                                               (*COMPLETADO*)
		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},nl)) = 
		    let 
		        val {exp=initE, ty=iniTy} = trexp init
		    in 
		        if tiposIguales iniTy TNil then error("no se puede determinar el tipo de "^name, nl)
		                                   else (tabRInserta (name, Var {ty=iniTy}, venv), tenv, [])
		    end                                                          (*COMPLETADO*)
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},nl)) =
		    let 
		        val sTy = (case tabBusca (s, tenv) of
		                    SOME t => t
		                    | NONE => error("No existe el tipo", nl))
		        val {exp=initE, ty=iniTy} = trexp init
		    in 
		        if tiposIguales iniTy sTy then (tabRInserta (name, Var {ty=iniTy}, venv), tenv, [])
		                                  else error("No coinciden los tipos", nl)
		    end                                                             (*COMPLETADO*)
		| trdec (venv,tenv) (FunctionDec fs) = 
		    let
		        val pnl = #2(List.hd fs)
		        val _ = if (Binaryset.numItems (Binaryset.addList ((Binaryset.empty String.compare), (List.map (#name o #1) fs))) <> List.length fs) 
		                then error("multiples declaraciones de una funcion en un batch", pnl) else ()
		        fun getFormals (ps, nl) = List.map (fn {typ, ... } => trty (typ, nl)) ps
		        fun genFuncEntry ({name, params, result=NONE, body}, nl) = (name, Func {level=mainLevel, label=tigertemp.newlabel(), 
		                                                                         formals = getFormals(params, nl), 
		                                                                         extern=false, result=TUnit})
		        | genFuncEntry ({name, params, result=SOME t, body}, nl) = (case tabBusca(t,tenv) of
		                                            SOME typ => (name, Func {level=mainLevel, label=tigertemp.newlabel(), 
		                                                              formals = getFormals(params, nl), extern=false, 
		                                                              result=typ})
		                                            | NONE => error("No existe el tipo "^t, nl))
		        val venv' = tigertab.tabInserList (venv, List.map genFuncEntry fs)
		        fun trbody (({name, params, result, body}, nl), env) = 
		            let 
		                val env'' : venv = List.foldl (fn ({typ, name, ...}, e) => tabInserta(name, Var {ty=trty(typ, nl)}, e)) env params
		                val {ty=bodyTy, ...} = transExp(env'', tenv) body
		                val _ = (case result of
		                            NONE => if not(tiposIguales bodyTy TUnit) then error("La funcion "^name^" no debe devolver nada", nl) 
		                                                                      else ()
		                            | SOME st => (case tabBusca(st, tenv) of
		                                            SOME t => if not(tiposIguales bodyTy t) then error("Error de tipo de retorno de la funcion "^name, nl)
		                                                                                    else ()
		                                            | NONE => error("No existe el tipo "^st, nl)))
		            in () end
		        val _ = List.map (fn f => trbody(f, venv')) fs
		    in 
		        (venv', tenv, []) 
		    end                                                         (* COMPLETADO *)
		| trdec (venv, tenv) (TypeDec []) = (venv, tenv, [])
		| trdec (venv, tenv) (TypeDec ts) =
			let 
				val nl = #2(hd ts)
				val _ = if (Binaryset.numItems (Binaryset.addList ((Binaryset.empty String.compare), (List.map (#name o #1) ts))) <> List.length ts) 
		                then error("multiples declaraciones de un tipo en un batch", nl) else ()
				val ltdec = List.map (#1) ts
				val tenv' = (topsort.fijaTipos ltdec tenv)
				                    handle Ciclo => error("existe un ciclo en la definicion de tipos", nl)
		    in (venv, tenv', [])
		    end                                             (* COMPLETADO *)
		    
	    and trty (NameTy s, nl) = (case tabBusca(s, tenv) of
		                                        NONE => error("No existe el tipo "^s, nl)
		                                        | SOME ty => ty)
		|   trty (RecordTy fs, nl)  = let val l = List.map (fn {name, escape, typ} => (name, trty(typ, nl), 0)) fs
		                              in TRecord (l, ref ()) end
		|   trty (ArrayTy s, nl)    = (case tabBusca(s, tenv) of
		                                        SOME (TArray (t, u)) => TArray (t, u)
		                                        | SOME _ => error(s^" no es un arreglo", nl)
		                                        | NONE => error("No existe el tipo "^s, nl))
	in trexp end


fun transProg ex =
	let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=NONE, body=ex}, 0)]],
						body=UnitExp 0}, 0)
		val _ = transExp(tab_vars, tab_tipos) main
	in	print "bien!\n" end
end

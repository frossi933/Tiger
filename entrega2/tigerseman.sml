structure tigerseman :> tigerseman =
struct

  open tigerabs
  open tigersres
  open tigertrans
  open topsort

  type expty = {exp: unit, ty: Tipo}

  type venv = (string, EnvEntry) tigertab.Tabla
  type tenv = (string, Tipo) tigertab.Tabla

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

  fun showTenv env = List.foldl (fn ((n,t),res) => n^"->"^printTipo t^"\n"^res) "" (tabAList env)


  val tab_tipos : tenv = tabInserList(
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

  fun transExp (venv, tenv) : expty =
    let
      fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
      fun trexp(VarExp v) = trvar(v)
      | trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
      | trexp(NilExp _)= {exp=nilExp(), ty=TNil}
      | trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt}
      | trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
      | trexp(CallExp({func=name, args}, nl)) =
        let
          val (expf, tyf) = (case tabBusca(name, venv) of
                    SOME (Func {formals, result, extern, level, label}) =>
                      let
                        fun getExptyOfArgs a = let val {exp, ty} = trexp a in (exp, ty) end
                        val (lexp, lty) = ListPair.unzip (List.map getExptyOfArgs args)
                        val _ = if not(eqList tiposIguales lty formals) then error("Argumentos incorrectos", nl)
                                                                        else ()
                        val isproc = (result=TUnit)
                        val expf' = callExp(label, isproc, extern, level, lexp)
                      in
                        (expf', result)
                      end
                    | SOME _                            => error(name^" no es una funcion", nl)
                    | NONE                              => error(name^" no existe", nl))
        in
          {exp=expf, ty=tyf}
        end
        (*COMPLETADO*)
      | trexp(OpExp({left, oper=EqOp, right}, nl)) =
        let
          val {exp=expl, ty=tyl} = trexp left
          val {exp=expr, ty=tyr} = trexp right
        in
          if
            (tiposIguales tyl tyr) andalso not(tyl=TNil andalso tyr=TNil) andalso (tyl<>TUnit)
          then
            {exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=EqOp,right=expr} else binOpIntRelExp {left=expl,oper=EqOp,right=expr},
             ty=TInt}
          else error("Tipos no comparables", nl)
        end
      | trexp(OpExp({left, oper=NeqOp, right}, nl)) =
        let
          val {exp=expl, ty=tyl} = trexp left
          val {exp=expr, ty=tyr} = trexp right
        in
          if
            (tiposIguales tyl tyr) andalso not(tyl=TNil andalso tyr=TNil) andalso (tyl<>TUnit)
          then
            {exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=NeqOp,right=expr} else binOpIntRelExp {left=expl,oper=NeqOp,right=expr},
             ty=TInt}
          else error("Tipos no comparables", nl)
        end
      | trexp(OpExp({left, oper, right}, nl)) =
        let
          val {exp=expl, ty=tyl} = trexp left
          val {exp=expr, ty=tyr} = trexp right
        in
          if tiposIguales tyl tyr then
            case oper of
              PlusOp => if tiposIguales (tipoReal tyl) TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt}
                                                            else error("Error de tipos", nl)
              | MinusOp => if tiposIguales (tipoReal tyl) TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt}
                                                               else error("Error de tipos", nl)
              | TimesOp => if tiposIguales (tipoReal tyl) TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt}
                                                               else error("Error de tipos", nl)
              | DivideOp => if tiposIguales (tipoReal tyl) TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt}
                                                                else error("Error de tipos", nl)
              | LtOp => if
                          (tiposIguales (tipoReal tyl) TInt) orelse (tiposIguales (tipoReal tyl) TString)
                        then
                          {exp=if tiposIguales (tipoReal tyl) TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},
                           ty=TInt}
                        else error("Error de tipos", nl)
              | LeOp => if
                          (tiposIguales (tipoReal tyl) TInt) orelse (tiposIguales (tipoReal tyl) TString)
                        then
                          {exp=if tiposIguales (tipoReal tyl) TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},
                           ty=TInt}
                        else error("Error de tipos", nl)
              | GtOp => if
                          (tiposIguales (tipoReal tyl) TInt) orelse (tiposIguales (tipoReal tyl) TString)
                        then
                          {exp=if tiposIguales (tipoReal tyl) TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},
                           ty=TInt}
                        else error("Error de tipos", nl)
              | GeOp => if
                          (tiposIguales (tipoReal tyl) TInt) orelse (tiposIguales (tipoReal tyl) TString)
                        then
                          {exp=if tiposIguales (tipoReal tyl) TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},
                           ty=TInt}
                        else error("Error de tipos", nl)
              | _ => raise Fail "No deberi­a pasar! (3)"
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

          (* Verificar que cada campo esta en orden y tenga una expresion del tipo que corresponde *)
          fun verificar _ [] [] = []
            | verificar _ (c::cs) [] = error("Faltan campos", nl)
            | verificar _ [] (c::cs) = error("Sobran campos", nl)
            | verificar n ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
              if s<>sy then error("Error de campo", nl)
                       else if tiposIguales ty t then (exp, n)::(verificar (n+1) cs ds)
                                                 else error("Error de tipo del campo "^s, nl)
          val lf = verificar 0 cs tfields   (*deberia estar ordenados de alguna manera para ir comparandolos*)
        in
          {exp=recordExp lf, ty=tyr}
        end
      | trexp(SeqExp(s, nl)) =
        let
          val lexti = map trexp s
          val exprs = map (fn{exp, ty} => exp) lexti
          val tipo = #ty hd(rev lexti)
        in
          {exp=seqExp (exprs), ty=tipo}
        end
      | trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
        let
          val {exp=eExp, ty=tyExp} = trexp exp
          val vExp = (case tabBusca(s, venv) of
                        SOME (Var {ty=TROInt,...})     => error("Entero de solo lectura", nl)
                        | SOME (Var {ty,access,level}) => if tiposIguales tyExp ty then simpleVar(access,level)
                                                                                   else error("Error de tipo de la expresion", nl)
                        | SOME (Func _)                => error("Asignacion incorrecta", nl)
                        | NONE                         => error("No existe variable", nl))
        in
          {exp=assignExp{var=vExp, exp=eExp}, ty=TUnit}
        end
      | trexp(AssignExp({var, exp}, nl)) =
        let
          val {ty=tyVar, exp=eVar} = trvar (var,nl)
          val {ty=tyExp, exp=eExp} = trexp exp
        in
          if tiposIguales tyVar tyExp then {exp=assignExp{var=eVar, exp=eExp}, ty=TUnit}
                                      else error("Asignacion incorrecta", nl)
        end
      | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
        let
          val {exp=testexp, ty=tytest} = trexp test
          val {exp=thenexp, ty=tythen} = trexp then'
          val {exp=elseexp, ty=tyelse} = trexp else'
        in
          if
            (tipoReal tytest=TInt) andalso (tiposIguales tythen tyelse)
          then
            {exp=if tipoReal tythen=TUnit then ifThenElseExpUnit {test=testexp,then'=thenexp,else'=elseexp}
                                          else ifThenElseExp {test=testexp,then'=thenexp,else'=elseexp},
             ty=tythen}
          else error("Error de tipos en if" ,nl)
        end
      | trexp(IfExp({test, then', else'=NONE}, nl)) =
        let
          val {exp=exptest,ty=tytest} = trexp test
          val {exp=expthen,ty=tythen} = trexp then'
        in
          if tipoReal tytest=TInt andalso tythen=TUnit then {exp=ifThenExp{test=exptest, then'=expthen}, ty=TUnit}
                                                       else error("Error de tipos en if", nl)
        end
      | trexp(WhileExp({test, body}, nl)) =
        let
          val ttest = trexp test
          val tbody = trexp body
        in
          if
            (tiposIguales (tipoReal (#ty ttest)) TInt) andalso (#ty tbody = TUnit)
          then
            {exp=whileExp {test=(#exp ttest), body=(#exp tbody), lev=topLevel()},
             ty=TUnit}
          else if not(tiposIguales (tipoReal (#ty ttest)) TInt) then error("Error de tipo en la condición", nl)
                                                                else error("El cuerpo de un while no puede devolver un valor", nl)
        end
      | trexp(ForExp({var, escape, lo, hi, body}, nl)) =
        let
          val {ty=tyLo, exp=expLo} = trexp lo
          val _ = if (tyLo <> TInt) andalso (tyLo <> TROInt) then error("El rango inferior de iteracion no es un entero", nl)
                                                             else ()
          val {ty=tyHi, exp=expHi} = trexp hi
          val _ = if (tyHi <> TInt) andalso (tyHi <> TROInt) then error("El rango superior de iteracion no es un entero", nl)
                                                             else ()
          val acc' = allocLocal (topLevel()) (!escape)
          val venv' = tabRInserta(var, Var {ty=TROInt, access=acc', level=getActualLev()}, venv)
          val vExp = simpleVar(acc',getActualLev())
          val {ty=tyBody, exp=expBody} = transExp (venv', tenv) body
        in
          if tyBody=TUnit then {exp=forExp{lo=expLo, hi=expHi, var=vExp, body=expBody}, ty=TUnit}
                          else error("El cuerpo debe devolver Unit", nl)
        end
      | trexp(LetExp({decs, body}, _)) =
        let
          fun processDec (dec, (venv_, tenv_, exps1)) =
            let
              val (venv__, tenv__, exps2) = trdec (venv_, tenv_) dec
            in
              (venv__, tenv__, exps1@exps2)
            end
  (*        val _ = (print "ENTORNOOOOOOO ANTS #################\n"; (print o showTenv) tenv;print "FIN #################\n") *)
          val (venv', tenv', expdecs) = List.foldl processDec (venv, tenv, []) decs
  (*        val _ = (print "ENTORNOOOOOOO DSP #################\n"; (print o showTenv) tenv';print "FIN #################\n") *)
          val {exp=expbody, ty=tybody} = transExp(venv', tenv') body
        in
          {exp=seqExp(expdecs@[expbody]), ty=tybody}
        end
      | trexp(BreakExp nl) =
        {exp=breakExp(), ty=TUnit}
      | trexp(ArrayExp({typ, size, init}, nl)) =
        let
          val {ty=sizTy, exp=sExp} = trexp size
          val _ = if not(tiposIguales sizTy TInt) then error("El tamaño del arreglo no es un numero", nl)
                                                  else ()
          val (resty,typTy) = (case tabBusca (typ, tenv) of
                            SOME (ty as (TArray (t,_))) => (ty,t)
                            | SOME _                    => error(typ^" no es un arreglo", nl)
                            | NONE                      => error("No existe el tipo "^typ, nl))
          val {ty=iniTy, exp=iniExp} = trexp init
          val _ = if not (tiposIguales iniTy typTy) then error("No coincide el tipo del inicializador", nl)
                                                    else ()
        in
          {exp=arrayExp{size=sExp, init=iniExp}, ty=resty}
        end
      and trvar(SimpleVar s, nl) =
        (case tabBusca (s, venv) of
              SOME (Var {ty, access, level}) => {exp=simpleVar(access,level), ty=ty}
              | SOME _                       => error(s^" no es una variable", nl)
              | _                            => error("No existe "^s, nl))
      | trvar(FieldVar(v, s), nl) =
        let
          val {ty=vTy, exp=vExp} = trvar(v, nl)
          val (sTy, sInt) = (case vTy of
                              TRecord (l,u) => (case List.find (fn (n, _, _) => n=s) l of
                                                      SOME (n, t, i) => (t,i)
                                                      | _            => error(s^" no es un campo del record", nl))
                              | _           => error("La variable no es un record", nl))
        in
          {exp=fieldVar(vExp, sInt), ty=sTy}
        end
      | trvar(SubscriptVar(v, e), nl) =
        let
          val {ty=vTy,exp=vExp} = trvar(v, nl)
          val resTy = (case vTy of
                        TArray (t, u) => t
                        | _           => error("La variable no es un arreglo", nl))
          val {exp=eExp, ty=eTy} = trexp e
          val _ = if not(tiposIguales eTy TInt) then error("El indice del arreglo no es un entero", nl)
                                                else ()
        in
          {exp=subscriptVar(vExp,eExp), ty=resTy}
        end
      and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},nl)) =
        let
          (*val _ = (print ("tenv para "^name^"\n"); print (showTenv tenv); print "fin\n")*)
          val {exp=initE, ty=iniTy} = transExp (venv, tenv) init
          val acc'=allocLocal (topLevel()) (!escape)
        in
          if iniTy=TNil then error("no se puede determinar el tipo de "^name, nl)
                        else (tabRInserta (name, Var {ty=iniTy, access=acc', level=getActualLev() }, venv), tenv, [])
        end                                                          (*COMPLETADO*)
      | trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},nl)) =
        let
          val sTy = (case tabBusca (s, tenv) of
                      SOME t => t
                      | NONE => error("No existe el tipo1", nl))
          val {exp=initE, ty=iniTy} = transExp (venv, tenv) init
          val acc'=allocLocal (topLevel()) (!escape)
        in
          if tiposIguales iniTy sTy then (tabRInserta (name, Var {ty=sTy, access=acc', level=getActualLev()}, venv), tenv, [])
                                    else error("No coinciden los tipos", nl)
        end                                                             (*COMPLETADO*)
      | trdec (venv,tenv) (FunctionDec fs) =
        let
  (*      val _ = print "function" *)
  (*      val _ = (print "entorno en la funcion\n"; (print o showTenv) tenv;print "FIN\n")*)
          val primerNl = #2(List.hd fs)
          val _ = if (Binaryset.numItems (Binaryset.addList ((Binaryset.empty String.compare), (List.map (#name o #1) fs))) <> List.length fs)
                  then error("multiples declaraciones de una funcion en un batch", primerNl)
                  else ()
          fun procFormals (params, nl) = List.map (fn {typ, escape, ... } => (trty (typ, tenv, nl), !escape)) params
          fun genFuncEntry ({name, params, result=NONE, body}, nl) =
            let(*let val _ = print name*)
              val (formalsTips, formalsBool) = ListPair.unzip (procFormals(params,nl))
              val (lev', label')= if name="_tigermain" then (outermost, name)
                                                       else let
                                                              val lab = (tigertemp.newlabel())^name
  							                                					  in
                                                              (newLevel {parent=topLevel(), name=lab, formals=formalsBool}, lab)
                                                            end
            in
              (name, Func {level=lev', label=label', formals = formalsTips, extern=false, result=TUnit})
            end
          | genFuncEntry ({name, params, result=SOME t, body}, nl) =
            let(*let val _ = print name*)
            in (case tabBusca(t,tenv) of
                  SOME typ => let
                                val (formalsTips, formalsBool) = ListPair.unzip (procFormals(params,nl))
                                val lab = tigertemp.newlabel()^name
                                val lev'= newLevel {parent=topLevel(), name=lab, formals=formalsBool}
                              in
                                (name, Func {level=lev', label=lab, formals = formalsTips, extern=false, result=typ})
                              end
                  | NONE   => error("No existe el tipo2 "^t, nl))
            end
          val venv' = tigertab.tabInserList (venv, List.map genFuncEntry fs)
  			  val _ = preFunctionDec()
          fun trbody (({name, params, result, body}, nl), env) =
            let
              val lev = (case tabBusca (name, env) of
                          SOME (Func {level, ...}) => level
                          | _                      => error("error interno en functiondec",nl))
              val _ = pushLevel lev
              fun insertParams ({typ, name, escape}, env') =
                let
                  val accvar = allocArg (topLevel()) (!escape)
  							in
                  tabInserta(name, Var {ty=trty(typ,tenv,nl),access=accvar,level=getActualLev()}, env')
                end
  					  val env'' = List.foldl insertParams env params (* ver si es necesario el static link aca *)

  (*                    fun insertParams ({typ, name, escape},(acs,e)) =
  						let	val accvar = allocArg (topLevel()) (!escape)
  						in	((accvar::acs), tabInserta(name, Var {ty=trty(typ,tenv,nl), access=accvar,level=getActualLev() },e))
  						end
                      val (accs, env'') = List.foldl insertParams ([],env) params
                      val accs' = accs 			tigerframe.slAccess() :: accs
                      val lev = (case tabBusca (name, env) of
                                    SOME (Func {level, label, formals, result, extern}) =>
  						((List.app tigerframe.accStr accs');
  						let val newLevel = tigertrans.insertAccs level accs'
  							val _ = tabRInserta(name, Func {level=newLevel, label=label, formals=formals, result=result, extern=extern}, env)
  						in newLevel
  						end)
                                    | _ => error("error interno en functiondec",nl))
  					val _ = pushLevel lev*)
  					  val {ty=bodyTy, exp=bodyExp} = transExp(env'', tenv) body
              val _ = tigertrans.functionDec(bodyExp, topLevel(), (result=NONE))
              val _ = (case result of
                        NONE      => if not(tiposIguales bodyTy TUnit) then error("La funcion "^name^" no debe devolver nada", nl)
                                                                       else ()
                        | SOME st => (case tabBusca(st, tenv) of
                                        SOME t => if not(tiposIguales bodyTy t) then error("Error de tipo de retorno de la funcion "^name, nl)
                                                                                else ()
                                        | NONE => error("No existe el tipo3 "^st, nl)))
              val _ = popLevel()
            in
              ()
            end
          val _ = List.map (fn f => trbody(f, venv')) fs
  			  val _ = postFunctionDec()
        in
          (venv', tenv, [])
        end                                                         (* COMPLETADO *)
      | trdec (venv, tenv) (TypeDec []) = (venv, tenv, [])
      | trdec (venv, tenv:tenv) (TypeDec ts) =
        let
          val nl = #2(hd ts)
          val _ = if (Binaryset.numItems (Binaryset.addList ((Binaryset.empty String.compare), (List.map (#name o #1) ts))) <> List.length ts)
                  then error("multiples declaraciones de un tipo en un batch", nl) else ()
          val ltdec = List.map (#1) ts
          (*val _ = (print "ENTORNOOOOOOO ANTES #################\n"; (print o showTenv) tenv;print "FIN #################\n")*)
          val tenv' = (topsort.fijaTipos ltdec tenv)
          (*val _ = (print "ENTORNOOOOOOOO DESPUEST #################\n"; (print o showTenv) tenv';print "FIN #################\n")*)
                              (* handle Ciclo => error("existe un ciclo en la definicion de tipos", nl) *)
        in
          (venv, tenv', [])
        end                                             (* COMPLETADO *)
      and trty (NameTy s, tenv', nl) = (case tabBusca(s, tenv') of
                                          NONE      => error("No existe el tipo4 "^s, nl)
                                          | SOME ty => ty)
      | trty (RecordTy fs, tenv', nl) =
        let
          val l = List.map (fn {name, escape, typ} => (name, trty(typ, tenv', nl), 0)) fs
        in
          TRecord (l, ref ())
        end
      | trty (ArrayTy s, tenv', nl) = (case tabBusca(s, tenv') of
                                        SOME (TArray (t, u)) => TArray (t, u)
                                        | SOME _             => error(s^" no es un arreglo", nl)
                                        | NONE               => error("No existe el tipo "^s, nl))
    in
      trexp
    end


  fun transProg ex =
    let
      val main = LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
                                             result=NONE, body=SeqExp ([ex, UnitExp 0],~1)}, 0)]],
                         body=UnitExp 0}, 0)
      val _ = transExp(tab_vars, tab_tipos) main
    in
      print "bien!\n"
    end

end

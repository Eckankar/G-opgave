(* vim: set ts=2 sw=2 sts=2 expandtab: *)
structure Type :> Type =
struct

  (* Use "raise Error (message,position)" for error messages *)
  exception Error of string*(int*int)

  type pos = int*int

  datatype Type = Int | Bool | TyVar of string

  (* lookup function for symbol table as list of (name,value) pairs *)
  fun lookup x []
        = NONE
    | lookup x ((y,v)::table)
        = if x=y then SOME v else lookup x table

  (* combine two symbol tables and check for duplicates *)
  fun combineTables [] table2 p = table2
    | combineTables ((x,v)::table1) table2 p =
        case lookup x table2 of
          SOME _ => raise Error ("Repeated identifier "^x,p)
        | NONE => (x,v) :: combineTables table1 table2 p

  (* check that type expression is valid and return its type *)
  fun checkType te ttable =
    case te of
      Cat.Int _ => Int
    | Cat.Bool _ => Bool
    | Cat.TyVar (n, _) => TyVar n

  (* Check pattern and return vtable *)
  fun checkPat pat ty ttable pos =
    case (pat,ty) of
      (Cat.NumP _, Int) => []
    | (Cat.TrueP _, Bool) => []
    | (Cat.FalseP _, Bool) => []
    | (Cat.NullP _, TyVar _) => []
    | (Cat.VarP (x,p), ty) => [(x,ty)]
    | (Cat.TupleP (ps, pos), TyVar t) =>
        let
          val ts = (case lookup t ttable of
                      SOME types => types
                    | NONE => raise Error ("Non-existing type "^t, pos))
        in
          if List.length ts = List.length ps
          then
            ListPair.foldr (fn (p, t, vs) =>
              combineTables (checkPat p t ttable pos) vs pos
            ) [] (ps, ts)
          else raise Error ("Tuple size doesn't match type", pos)
        end
    | _ => raise Error ("Pattern doesn't match type", pos)

  (* Rewrites a let statement to a nested sequence of case statements *)
  fun letToCase [] e0 pos = e0
    | letToCase ((p, e, pos)::decs) e0 pos =
      Cat.Case (e, [(p, letToCase decs e0 pos)], pos)

  (* check expression and return type *)
  fun checkExp exp vtable ftable ttable =
    case exp of
      Cat.Num (n,pos) => Int
    | Cat.True (pos)  => Bool
    | Cat.False (pos) => Bool
    | Cat.Null (name, pos) =>
        (case lookup name ttable of
           SOME _ => TyVar name
         | NONE   => raise Error ("Unknown type "^name, pos))
    | Cat.Var (x,pos) =>
       (case lookup x vtable of
          SOME t => t
        | _ => raise Error ("Unknown variable "^x,pos))
    | Cat.Plus (e1,e2,pos) =>
       (case (checkExp e1 vtable ftable ttable,
              checkExp e2 vtable ftable ttable) of
          (Int,Int) => Int
        | _ => raise Error ("Non-int argument to +",pos))
    | Cat.Minus (e1,e2,pos) =>
       (case (checkExp e1 vtable ftable ttable,
              checkExp e2 vtable ftable ttable) of
          (Int,Int) => Int
        | _ => raise Error ("Non-int argument to -",pos))
    | Cat.Equal (e1, e2, pos) =>
        let
          val t1 = checkExp e1 vtable ftable ttable;
          val t2 = checkExp e2 vtable ftable ttable
        in
          if t1 = t2 andalso (t1 = Int orelse t1 = Bool)
          then Bool
          else raise Error ("Different type arguments to =", pos)
        end
    | Cat.Less (e1, e2, pos) =>
        (case (checkExp e1 vtable ftable ttable,
               checkExp e2 vtable ftable ttable) of
            (Int, Int) => Bool
          | _ => raise Error ("Non-int argument to <", pos))
    | Cat.Not (e, pos) =>
        (case checkExp e vtable ftable ttable of
            Bool => Bool
          | _ => raise Error ("Non-bool argument to not", pos))
    | Cat.And (e1, e2, pos) =>
        (case (checkExp e1 vtable ftable ttable,
               checkExp e2 vtable ftable ttable) of
            (Bool, Bool) => Bool
          | _ => raise Error ("Non-bool argument to and", pos))
    | Cat.Or (e1, e2, pos) =>
        (case (checkExp e1 vtable ftable ttable,
               checkExp e2 vtable ftable ttable) of
            (Bool, Bool) => Bool
          | _ => raise Error ("Non-bool argument to and", pos))
    | Cat.Let (decs, exp, pos) =>
        checkExp (letToCase decs exp pos) vtable ftable ttable
    | Cat.If (cond, e1, e2, pos) =>
        let
          val ctype = checkExp cond vtable ftable ttable;
          val t1 = checkExp e1 vtable ftable ttable;
          val t2 = checkExp e2 vtable ftable ttable
        in
          if ctype = Bool
          then
            if t1 = t2
            then t1
            else raise Error ("Non-matching expression types in if", pos)
          else raise Error ("Non-boolean condition in if", pos)
        end
    | Cat.MkTuple (exps, name, pos) =>
      let
        val expType = map (fn x => checkExp x vtable ftable ttable) exps;
        val decType = (case lookup name ttable of
                          SOME t => t
                        | NONE   => raise Error ("Non-existing type "^name,pos))
      in
        if expType = decType
        then TyVar name
        else raise Error ("Expression doesn't match type "^name,pos)
      end
    | Cat.Case (e, m, pos) =>
      let
        val etype = checkExp e vtable ftable ttable;
      in
        checkMatch m etype vtable ftable ttable pos
      end
    | Cat.Apply (f,e1,pos) =>
       (case lookup f ftable of
            SOME (t1,t2) =>
              if t1 = (checkExp e1 vtable ftable ttable)
              then t2
              else raise Error ("Argument does not match declaration of "^f,pos)
          | _ => raise Error ("Unknown function "^f,pos))
    | Cat.Read (n,pos) => Int
    | Cat.Write (e1,pos) =>
       (case checkExp e1 vtable ftable ttable of
          Int => Int
        | _ => raise Error ("Non-int argument to write",pos))

  and checkMatch [(p,e)] tce vtable ftable ttable pos =
        let
          val vtable1 = checkPat p tce ttable pos
        in
          checkExp e (vtable1 @ vtable) ftable ttable
        end
    | checkMatch ((p,e)::ms) tce vtable ftable ttable pos =
        let
          val vtable1 = checkPat p tce ttable pos
          val te = checkExp e (vtable1 @ vtable) ftable ttable
          val tm = checkMatch ms tce vtable ftable ttable pos
        in
          if te = tm then te
          else raise Error ("Match branches have different type",pos)
        end
    | checkMatch [] tce vtable ftable ttable pos =
        raise Error ("Empty match",pos)

  (* builds a table of the declared types *)
  fun getTyDecs [] ttable = ttable
    | getTyDecs ((name, tlist, pos)::ts) ttable =
      if List.exists (fn (n,_)=>n=name) ttable
      then raise Error ("Duplicate declaration of type "^name, pos)
      else getTyDecs ts
      ((name, List.map (fn t => checkType t ttable) tlist) :: ttable)

  (* builds a table of the declared functions *)
  fun getFunDecs [] ttable ftable = ftable
    | getFunDecs ((f, targ, tresult, m, pos)::fs) ttable ftable =
        if List.exists (fn (g,_)=>f=g) ftable
        then raise Error ("Duplicate declaration of function "^f,pos)
        else getFunDecs fs ttable
          ((f, (checkType targ ttable, checkType tresult ttable)) :: ftable)

  (* checks validity of declared types *)
  fun checkTyDec ttable (name, [], _) = name
    | checkTyDec ttable (name, (Cat.TyVar (tn, tpos)) :: tlist, pos) =
        (case lookup tn ttable of
          SOME _ => checkTyDec ttable (name, tlist, pos)
        | NONE   =>
      raise Error ("Unknown type "^tn^" used in type declaration", tpos))
    | checkTyDec ttable (name, _ :: tlist, pos) =
        checkTyDec ttable (name, tlist, pos)

  (* checks types of declared functions *)
  fun checkFunDec ftable ttable (f, targ, tresult, m, pos) =
    let
      val argtype = checkType targ ttable
      val resulttype = checkType tresult ttable
      val bodytype = checkMatch m argtype [] ftable ttable pos
    in
      if resulttype = bodytype
      then resulttype
      else raise Error ("Body type doesn't match declaration",pos)
    end

  fun checkProgram (tyDecs, funDecs, e) =
    let
      val ttable = getTyDecs tyDecs []
      val _ = List.map (checkTyDec ttable) tyDecs
      val ftable = getFunDecs funDecs ttable []
      val _ = List.map (checkFunDec ftable ttable) funDecs
    in
      (checkExp e [] ftable ttable; ())
    end
end

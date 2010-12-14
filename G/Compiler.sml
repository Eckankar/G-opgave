(* vim: set ts=2 sw=2 sts=2 expandtab: *)
(* Compiler for Cat *)
(* Compile by mosmlc -c Compiler.sml *)
(* Then recompile CC by mosmlc CC.sml -o CC *)

structure Compiler :> Compiler =
struct

  (* Use "raise Error (message,position)" for error messages *)
  exception Error of string*(int*int)

  (* Name generator.  Call with, e.g., t1 = "tmp"^newName () *)
  val counter = ref 0

  fun newName () = (counter := !counter + 1;
                  "_" ^ Int.toString (!counter)^ "_")

  (* Number to text with spim-compatible sign symbol *)
  fun makeConst n = if n>=0 then Int.toString n
                    else "-" ^ Int.toString (~n)

  fun lookup x [] pos = raise Error ("Name "^x^" not found", pos)
    | lookup x ((y,v)::table) pos = if x=y then v else lookup x table pos

  fun isIn x [] = false
    | isIn x (y::ys) = x=y orelse isIn x ys

  (* link register *)
  val RA = "31"
  (* Register for stack pointer *)
  val SP = "29"
  (* Register for heap pointer *)
  val HP = "28"

  (* Suggested register division *)
  val maxCaller = 15   (* highest caller-saves register *)
  val maxReg = 26      (* highest allocatable register *)

  (* Rewrites a let statement to a nested sequence of case statements *)
  fun letToCase [] e0 pos = e0
    | letToCase ((p, e, pos)::decs) e0 pos =
      Cat.Case (e, [(p, letToCase decs e0 pos)], pos)

  (* compile pattern *)
  fun compilePat p v vtable fail =
    case p of
      Cat.NumP (n,pos) =>
        let
          val t = "_constPat_"^newName()
        in
          if n<32768 then
            ([Mips.LI (t, makeConst n),
              Mips.BNE (v,t,fail)],
             vtable)
          else
            ([Mips.LUI (t, makeConst (n div 65536)),
              Mips.ORI (t, t, makeConst (n mod 65536)),
              Mips.BNE (v,t,fail)],
             vtable)
        end
    | Cat.TrueP (pos) =>
        ([Mips.BEQ (v, "0", fail)], vtable)
    | Cat.FalseP (pos) =>
        ([Mips.BNE (v, "0", fail)], vtable)
    | Cat.NullP (pos) =>
        ([Mips.COMMENT "Null pattern",
          Mips.BNE (v, "0", fail)], vtable)
    | Cat.VarP (x,pos) =>
        let
          val xt = "_patVar_"^x^"_"^newName()
        in
          ([Mips.MOVE (xt,v)], (x,xt)::vtable)
        end
    | Cat.TupleP (ps, pos) =>
        let
          val (code, _, nvtable) =
            foldl (fn (p, (a, i, vtable)) =>
                    let
                      val tp = "_tuplepp_"^newName()
                      val tv = "_tuplepv_"^newName()
                      val (code, nvtable) = compilePat p tv vtable fail
                    in
                      (a @ [Mips.LW (tv, v, makeConst i)] @ code, i+4, nvtable)
                    end) ([], 0, vtable) ps
        in
          ([Mips.COMMENT "Tuple pattern", Mips.BEQ (v, "0", fail)] @ code, nvtable)
        end

  (* compile expression *)
  fun compileExp e vtable place =
    case e of
      Cat.Num (n,pos) =>
        if n<32768 then
          [Mips.LI (place, makeConst n)]
        else
          [Mips.LUI (place, makeConst (n div 65536)),
          Mips.ORI (place, place, makeConst (n mod 65536))]
    | Cat.True (pos) => [Mips.LI (place, makeConst 1)]
    | Cat.False (pos) => [Mips.LI (place, makeConst 0)]
    | Cat.Null (name, pos) => [Mips.LI (place, makeConst 0)]
    | Cat.Var (x,pos) => [Mips.MOVE (place, lookup x vtable pos)]
    | Cat.Plus (e1,e2,pos) =>
        let
          val t1 = "_plus1_"^newName()
          val t2 = "_plus2_"^newName()
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
        in
          code1 @ code2 @ [Mips.ADD (place,t1,t2)]
        end
    | Cat.Minus (e1,e2,pos) =>
        let
          val t1 = "_minus1_"^newName()
          val t2 = "_minus2_"^newName()
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
        in
          code1 @ code2 @ [Mips.SUB (place,t1,t2)]
        end
    | Cat.Equal (e1, e2, pos) =>
        let
          val t1 = "_equal1_"^newName()
          val t2 = "_equal2_"^newName()
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
          val lequal = "_equall_"^newName()
          val ldone = "_equald_"^newName()
        in
          code1 @ code2 @ [Mips.BEQ (t1, t2, lequal),
                           Mips.LI (place, makeConst 0),
                           Mips.J ldone,
                           Mips.LABEL lequal,
                           Mips.LI (place, makeConst 1),
                           Mips.LABEL ldone]
        end
    | Cat.Less (e1, e2, pos) =>
        let
          val t1 = "_less1_"^newName()
          val t2 = "_less2_"^newName()
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
        in
          code1 @ code2 @ [Mips.SLT (place,t1,t2)]
        end
    | Cat.Not (e, pos) =>
        let
          val t = "_not_"^newName()
          val code = compileExp e vtable t
        in
          code @ [Mips.SLTI (place,t,"1")]
        end
    | Cat.And (e1, e2, pos) =>
        let
          val t1 = "_and1_"^newName()
          val t2 = "_and2_"^newName()
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
          val lfalse = "_andf_"^newName()
          val ldone = "_andd_"^newName()
        in
          code1 @ [Mips.BEQ (t1, "0", lfalse)]
                @ code2
                @ [Mips.BEQ (t2, "0", lfalse),
                   Mips.LI (place, makeConst 1),
                   Mips.J ldone,
                   Mips.LABEL lfalse,
                   Mips.LI (place, makeConst 0),
                   Mips.LABEL ldone]
        end
    | Cat.Or (e1, e2, pos) =>
        let
          val t1 = "_or1_"^newName()
          val t2 = "_or2_"^newName()
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
          val ltrue = "_ort_"^newName()
          val ldone = "_ord_"^newName()
        in
          code1 @ [Mips.BNE (t1, "0", ltrue)]
                @ code2
                @ [Mips.BNE (t2, "0", ltrue),
                   Mips.LI (place, makeConst 0),
                   Mips.J ldone,
                   Mips.LABEL ltrue,
                   Mips.LI (place, makeConst 1),
                   Mips.LABEL ldone]
        end
    | Cat.Let (decs, exp, pos) =>
        compileExp (letToCase decs exp pos) vtable place
    | Cat.If (cond, e1, e2, pos) =>
        let
          val tc = "_ifcond_"^newName()
          val t1 = "_if1_"^newName()
          val t2 = "_if2_"^newName()
          val codec = compileExp cond vtable tc
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
          val lfalse = "_iffalse_"^newName()
          val lend = "_ifend_"^newName()
        in
          codec @ [Mips.BEQ (tc, "0", lfalse)]
                @ code1
                @ [Mips.J lend, Mips.LABEL lfalse]
                @ code2
                @ [Mips.LABEL lend]
        end
    | Cat.MkTuple (exps, name, pos) =>
        let
          val tsize = length exps
          val thp = "_mktuplehp_"^newName()
        in
          [Mips.MOVE (thp, HP),
           Mips.ADDI (HP, HP, makeConst(4*tsize))] @
          #1 (foldl (fn (e, (a, i)) =>
                  let
                    val t = "_mktuple_"^newName()
                    val code = compileExp e vtable t
                  in
                    (a @ code @ [Mips.SW (t, thp, makeConst i)], i+4)
                  end)
                ([], 0) exps) @
          [Mips.MOVE (place, thp)]
        end
    | Cat.Case (e, m, pos) =>
        let
          val t = "_case_"^newName()
          val code = compileExp e vtable t
          val lend = "_casee_"^newName()
          val lerror = "_caseerror_"^newName()
        in
          code @
          compileMatch m t place lend lerror vtable @
          [Mips.LABEL lerror,
           Mips.LI ("5", makeConst (#1 pos)),
           Mips.J "_Error_",
           Mips.LABEL lend]
        end
    | Cat.Apply (f,e,pos) =>
        let
          val t1 = "_apply_"^newName()
          val code1 = compileExp e vtable t1
        in
          code1 @
          [Mips.MOVE ("2",t1), Mips.JAL (f,["2"]), Mips.MOVE (place,"2")]
        end
    | Cat.Read pos =>
        [Mips.LI ("2","5"), (* read_int syscall *)
         Mips.SYSCALL,
         Mips.MOVE (place,"2")]
    | Cat.Write (e,pos) =>
        compileExp e vtable place @
        [Mips.MOVE ("4",place),
         Mips.LI ("2","1"),  (* write_int syscall *)
         Mips.SYSCALL,
         Mips.LA ("4","_cr_"),
         Mips.LI ("2","4"),  (* write_string syscall *)
         Mips.SYSCALL]

  and compileMatch [] arg res endLabel failLabel vtable =
        [Mips.J failLabel]
    | compileMatch ((p,e)::m) arg res endLabel failLabel vtable =
        let
    val next = "_match_"^newName()
    val (code1, vtable1) = compilePat p arg vtable next
    val code2 = compileExp e vtable1 res
    val code3 = compileMatch m arg res endLabel failLabel vtable
  in
    code1 @ code2 @ [Mips.J endLabel, Mips.LABEL next] @ code3
  end

  (* code for saving and restoring callee-saves registers *)
  fun stackSave currentReg maxReg savecode restorecode offset =
    if currentReg > maxReg
    then (savecode, restorecode, offset)  (* done *)
    else stackSave (currentReg+1)
                   maxReg
                   (Mips.SW (makeConst currentReg,
                                 SP,
                                 makeConst offset)
                    :: savecode) (* save register *)
                   (Mips.LW (makeConst currentReg,
                                 SP,
                                 makeConst offset)
                    :: restorecode) (* restore register *)
                   (offset-4) (* adjust offset *)


  (* compile function declaration *)
  and compileFun (fname, argty, resty, m, (line,col)) =
        let
    val atmp = fname ^"_arg_"^ newName()
          val rtmp = fname ^"_res_"^ newName()
          val exit = fname ^"_return_"^ newName()
          val fail = fname ^"_fail_"^ newName()
    val parcode       (* move R2 to argument *)
            = [Mips.MOVE (atmp, "2")]
          val returncode    (* move return value to R2 *)
            = [Mips.LABEL exit, Mips.MOVE ("2",rtmp)]
          val errorcode     (* if match fails *)
      = [Mips.LABEL fail,
         Mips.LI ("5",makeConst line),
         Mips.J "_Error_"]
          val body = compileMatch m atmp rtmp exit fail []
          val (body1, _, maxr)  (* call register allocator *)
            = RegAlloc.registerAlloc
                (parcode @ body @ returncode) ["2"] 2 maxCaller maxReg
          val (savecode, restorecode, offset) = (* save/restore callee-saves *)
                stackSave (maxCaller+1) maxr [] [] (~8)
        in
            [Mips.COMMENT "",
             Mips.LABEL fname,  (* function label *)
             Mips.SW (RA, SP, "-4")] (* save return address *)
          @ savecode  (* save callee-saves registers *)
          @ [Mips.ADDI (SP,SP,makeConst offset)] (* move SP down *)
          @ body1  (* code for function body *)
          @ [Mips.ADDI (SP,SP,makeConst (~offset))] (* move SP up *)
          @ restorecode  (* restore callee-saves registers *)
          @ [Mips.LW (RA, SP, "-4"), (* restore return addr *)
             Mips.JR (RA, [])] (* return *)
    @ errorcode
        end


  (* compile program *)
  fun compile (tys, funs, e) =
    let
      val funsCode = List.concat (List.map compileFun funs)
      val mainCode = compileExp e [] "dead" @ [Mips.J "_stop_"]
      val (code1, _, _)
             = RegAlloc.registerAlloc mainCode [] 2 maxCaller maxReg
    in
      [Mips.TEXT "0x00400000",
       Mips.GLOBL "main",
       Mips.LABEL "main",
       Mips.LA (HP, "_heap_")]    (* initialise heap pointer *)
      @ code1                     (* run program *)
      @ funsCode      (* code for functions *)
      @ [Mips.LABEL "_stop_",
         Mips.LI ("2","10"),      (* syscall control = 10 *)
         Mips.SYSCALL,            (* exit *)
         Mips.LABEL "_Error_",    (* code for reporting match errors *)
   Mips.LA ("4","_ErrorString_"),
   Mips.LI ("2","4"), Mips.SYSCALL, (* print string *)
   Mips.MOVE ("4","5"),
   Mips.LI ("2","1"), Mips.SYSCALL, (* print line number *)
   Mips.LA ("4","_cr_"),
   Mips.LI ("2","4"), Mips.SYSCALL, (* print CR *)
   Mips.J "_stop_",
   Mips.DATA "",
   Mips.LABEL "_cr_",       (* carriage return string *)
   Mips.ASCIIZ "\n",
   Mips.LABEL "_ErrorString_",
   Mips.ASCIIZ "Match failed near line ",
   Mips.ALIGN "2",
   Mips.LABEL "_heap_",
   Mips.SPACE "100000"]
    end

end

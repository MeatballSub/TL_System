(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

(*
fun M( [[stmt1 ; stmtList1 ]], m0) = 
    let
        val m1 = M( stmt1, m0)
        val m2 = M(stmtList1, m1)
    in
        m2
    end
;

fun M( itree(inode("WFC_START",_), [ block1 ]), m0) = m0
itree(inode("{",_),[])
*)

(*<EXPRESSION>            ::= <EXPRESSION> "or" <DISJUNCTION>
                          | <DISJUNCTION>.

<DISJUNCTION>           ::= <DISJUNCTION> "and" <EQUALITY>
                          | <EQUALITY>.*)

fun E ( itree(inode("EXPRESSION",_), [disj1]), m0) = E(disj1, m0)
  | E ( itree(inode("EXPRESSION",_), [expr ,itree(inode("or",_), []), disjunction]), m0) =
    let
        val (v1, m1) = E(expr, m0);
        val (v2, m2) = if DVtoBool(v1) then (v1,m1) else
                            let
                                val (v3, m3) = E(disjunction, m1);
                                val v4 = if DVtoBool(v3) then Boolean(true) else Boolean(false)
                            in
                                (v4, m3)
                            end;
    in
        (v2, m2)
    end
  | E ( itree(inode("DISJUNCTION",_), [equality1]), m0) = E(equality1, m0)
  | E ( itree(inode("DISJUNCTION",_), [disj1, itree(inode("and",_),[]) ,equality1]), m0) =
    let
        val (v1, m1) = E(disj1, m0);
        val (v2, m2) = if DVtoBool(v1) then
                            let
                                val (v3, m3) = E(equality1, m1);
                                val v4 = if DVtoBool(v3) then Boolean(true) else Boolean(false)
                            in
                                (v4, m3)
                            end
                       else
                            (Boolean(false), m1);
    in
        (v2, m2)
    end
    
  | E ( itree(inode("EQUALITY",_), [relational1]), m0) = E(relational1, m0)

  | E ( itree(inode("EQUALITY",_), [equality1, itree(inode("==",_),[]), relational1]), m0) =
    let
        val (v1, m1) = E(equality1, m0);
        val (v2, m2) = E(relational1, m1);
        val v3 = if (v1 = v2) then Boolean(true) else Boolean(false);
    in
        (v3, m2)
    end

  | E ( itree(inode("EQUALITY",_), [equality1, itree(inode("!=",_),[]), relational1]), m0) =
    let
        val (v1, m1) = E(equality1, m0);
        val (v2, m2) = E(relational1, m1);
        val v3 = Boolean(v1 <> v2);
    in
        (v3, m2)
    end

  | E ( itree(inode("RELATIONAL",_),[additive1]),m0) = E(additive1, m0)
  | E ( itree(inode("RELATIONAL",_),[relational1, itree(inode("<",_),[]),additive1]),m0) =
    let
        val (v1, m1) = E(relational1, m0);
        val (v2, m2) = E(additive1, m1);
        val v3 = Boolean(DVtoInt(v1) < DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("RELATIONAL",_),[relational1, itree(inode("<=",_),[]),additive1]),m0) =
    let
        val (v1, m1) = E(relational1, m0);
        val (v2, m2) = E(additive1, m1);
        val v3 = Boolean(DVtoInt(v1) <= DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("RELATIONAL",_),[relational1, itree(inode(">",_),[]),additive1]),m0) =
    let
        val (v1, m1) = E(relational1, m0);
        val (v2, m2) = E(additive1, m1);
        val v3 = Boolean(DVtoInt(v1) > DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("RELATIONAL",_),[relational1, itree(inode(">=",_),[]),additive1]),m0) =
    let
        val (v1, m1) = E(relational1, m0);
        val (v2, m2) = E(additive1, m1);
        val v3 = Boolean(DVtoInt(v1) >= DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("ADDITIVE",_),[multiplicative1]),m0) = E(multiplicative1, m0)
  | E ( itree(inode("ADDITIVE",_),[additive1, itree(inode("+",_),[]), multiplicative1]),m0) =
    let
        val (v1, m1) = E(additive1, m0);
        val (v2, m2) = E(multiplicative1, m1);
        val v3 = Integer(DVtoInt(v1) + DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("ADDITIVE",_),[additive1, itree(inode("-",_),[]), multiplicative1]),m0) =
    let
        val (v1, m1) = E(additive1, m0);
        val (v2, m2) = E(multiplicative1, m1);
        val v3 = Integer(DVtoInt(v1) - DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("MULTIPLICATIVE",_),[exponential1]),m0) = E(exponential1, m0)
  | E ( itree(inode("MULTIPLICATIVE",_),[multiplicative1, itree(inode("*",_),[]), exponential1]),m0) =
    let
        val (v1, m1) = E(multiplicative1, m0);
        val (v2, m2) = E(exponential1, m1);
        val v3 = Integer(DVtoInt(v1) * DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("MULTIPLICATIVE",_),[multiplicative1, itree(inode("div",_),[]), exponential1]),m0) =
    let
        val (v1, m1) = E(multiplicative1, m0);
        val (v2, m2) = E(exponential1, m1);
        val v3 = Integer(DVtoInt(v1) div DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("MULTIPLICATIVE",_),[multiplicative1, itree(inode("mod",_),[]), exponential1]),m0) =
    let
        val (v1, m1) = E(multiplicative1, m0);
        val (v2, m2) = E(exponential1, m1);
        val v3 = Integer(DVtoInt(v1) mod DVtoInt(v2));
    in
        (v3, m2)
    end
    
  | E ( itree(inode("EXPONENTIAL",_),[unary1]),m0) = E(unary1, m0)
  | E ( itree(inode("EXPONENTIAL",_),[unary1, itree(inode("^",_),[]),exponential1]),m0) =
    let
        fun power(a,b) = if (b=0) then 1 else power(a,b-1)*a;
        val (v1, m1) = E(exponential1, m0);
        val (v2, m2) = E(unary1, m1);
        val v3 = Integer(power(DVtoInt(v2), DVtoInt(v1)));
    in
        (v3, m2)
    end
  
  | E ( itree(inode("UNARY",_),[primary1]),m0) = E(primary1, m0)
  | E ( itree(inode("UNARY",_),[itree(inode("-",_),[]), primary1]),m0) = 
    let
        val (v1, m1) = E(primary1, m0);
        val v2 = Integer(0 - (DVtoInt(v1)));
    in
        (v2, m1)
    end
    
  | E ( itree(inode("UNARY",_),[itree(inode("not",_),[]), primary1]),m0) = 
    let
        val (v1, m1) = E(primary1, m0);
        val v2 = Boolean(not(DVtoBool(v1)));
    in
        (v2, m1)
    end
    
  | E ( itree(inode("PRIMARY",_),[primary1]),m0) = E(primary1, m0)
  | E ( itree(inode("PRIMARY",_),[itree(inode("(",_),[]), expr1, itree(inode(")",_),[])]),m0) = E(expr1, m0)
  | E ( itree(inode("PREFIX_EXPRESSION",_),[itree(inode("++",_),[]), id1]),m0) =
    let
        val loc = getLoc(accessEnv(getLeaf(id1), m0));
        val v1 = Integer(DVtoInt(accessStore(loc, m0)) + 1);
        val m1 = updateStore(loc, v1, m0);
    in
        (v1, m1)
    end

  | E ( itree(inode("PREFIX_EXPRESSION",_),[itree(inode("--",_),[]), id1]),m0) =
    let
        val loc = getLoc(accessEnv(getLeaf(id1), m0));
        val v1 = Integer(DVtoInt(accessStore(loc, m0)) - 1);
        val m1 = updateStore(loc, v1, m0);
    in
        (v1, m1)
    end

  | E ( itree(inode("POSTFIX_EXPRESSION",_),[id1, itree(inode("++",_),[])]),m0) =
    let
        val loc = getLoc(accessEnv(getLeaf(id1), m0));
        val v1 = Integer(DVtoInt(accessStore(loc, m0)) + 1);
        val m1 = updateStore(loc, v1, m0);
    in
        (v1, m1)
    end

  | E ( itree(inode("POSTFIX_EXPRESSION",_),[id1, itree(inode("--",_),[])]),m0) =
    let
        val loc = getLoc(accessEnv(getLeaf(id1), m0));
        val v1 = Integer(DVtoInt(accessStore(loc, m0)) - 1);
        val m1 = updateStore(loc, v1, m0);
    in
        (v1, m1)
    end

  | E ( itree(inode("PRIMARY",_),[itree(inode("|",_),[]), expr1, itree(inode("|",_),[])]),m0) = 
    let
        val (v1, m1) = E(expr1, m0);
        val v2 = Integer(abs(DVtoInt(v1)));
    in
        (v2, m1)
    end
    
  | E ( itree(inode("boolean",_),[bool1]),m0) = if getLeaf(bool1) = "true" then (Boolean(true), m0) else (Boolean(false), m0)
    
  | E ( itree(inode("integer",_),[int1]),m0) = 
    let
        val v1 = valOf(Int.fromString(getLeaf(int1)));
    in
        (Integer(v1), m0)
    end

  | E ( itree(inode("identifier",_),[id1]),m0) = 
    let
        val loc = getLoc(accessEnv(getLeaf(id1), m0));
        val v = accessStore(loc, m0);
    in
        (v, m0)
    end

  | E ( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
  | E _ = raise Fail("error in Semantics.E - this should never occur");

fun M ( itree(inode("WFC_START",_), [ stmtlist1 ]), m0) =
    let
        val m1 = M(stmtlist1, m0);
        val p1 = showModel(m1);
    in
        m1
    end
    
  | M ( itree(inode("STATEMENT_LIST",_), [ epsilon ]), m0) =
    let
        val m1 = M(epsilon, m0);
    in
        m1
    end

  | M ( itree(inode("STATEMENT_LIST",_), [ stmt1, stmtlist1 ]), m0) =
    let
        val m1 = M(stmt1, m0);
        val m2 = M(stmtlist1, m1); 
    in
        m2
    end
    
  | M ( itree(inode("EPSILON",_), _), m0) = m0

  | M ( itree(inode("STATEMENT",_), [stmt1, itree(inode(";",_), [])]), m0) =
    let
        val m1 = M(stmt1, m0);
    in
        m1
    end
    
  | M ( itree(inode("STATEMENT",_), [stmt1]), m0) =
    let
        val m1 = M(stmt1, m0);
    in
        m1
    end
    
  | M ( itree(inode("DECLARATION_STATEMENT",_), [ itree(inode("int",_), []), id1 ]), m0) =
    let
        val m1 = updateEnvironment(getLeaf(id1), INT, new(m0), m0);
    in
        m1
    end
    
  | M ( itree(inode("DECLARATION_STATEMENT",_), [ itree(inode("bool",_), []), id1 ]), m0) =
    let
        val m1 = updateEnvironment(getLeaf(id1), BOOL, new(m0), m0);
    in
        m1
    end

  | M ( itree(inode("DECLARATION_STATEMENT",_), [ itree(inode("int",_), []), id1, itree(inode("=",_), []), expr1 ]), m0) =
    let
        val m1 = updateEnvironment(getLeaf(id1), INT, new(m0), m0);
        val (v, m2) = E(expr1, m1);
        val loc = getLoc(accessEnv(getLeaf(id1), m2));
        val m3 = updateStore(loc, v, m2);
    in
        m3
    end

  | M ( itree(inode("DECLARATION_STATEMENT",_), [ itree(inode("bool",_), []), id1, itree(inode("=",_), []), expr1 ]), m0) =
    let
        val m1 = updateEnvironment(getLeaf(id1), BOOL, new(m0), m0);
        val (v, m2) = E(expr1, m1);
        val loc = getLoc(accessEnv(getLeaf(id1), m2));
        val m3 = updateStore(loc, v, m2);
    in
        m3
    end

  | M ( itree(inode("ASSIGNMENT_STATEMENT",_), [ itree(inode("identifier",_), [id1]), itree(inode("=",_), []), expr1 ]), m0) =
    let
        val (v1, m1) = E(expr1, m0)
        val loc = getLoc(accessEnv(getLeaf(id1), m1))
        val m2 = updateStore(loc,v1,m1)
    in
        m2
    end
  | M ( itree(inode("ASSIGNMENT_STATEMENT",_), [ prePostFix ]), m0) =
    let
        val (v1, m1) =  E(prePostFix, m0)
    in
        m1
    end

  | M ( itree(inode("PRINT_STATEMENT",_), [prnt, itree(inode("(",_), []), expr, itree(inode(")",_), []) ]), m0) =
    let
        val (v1,m1) = E(expr, m0)
        val p = print(DVtoString(v1) ^ "\n");
    in
        m1
    end

  | M ( itree(inode("BLOCK",_), [ itree(inode("{",_), []), statementList, itree(inode("}",_), []) ]), m0) =
    let
        val m1 =  M(statementList, m0)
    in
        m1 
    end
    
  | M ( itree(inode("CONDITIONAL_STATEMENT",_), [itree(inode("if",_), []),itree(inode("(",_), []), expr, itree(inode(")",_), []), blk ]), m0) =
    let
        val (v1,m1) = E(expr, m0)
    in
        if DVtoBool(v1) then M(blk, m1) else m1
    end 
    
  | M ( itree(inode("CONDITIONAL_STATEMENT",_), [itree(inode("if",_), []),itree(inode("(",_), []), expr, itree(inode(")",_), []), blk, itree(inode("else",_), []), blk2 ]), m0) =
    let
        val (v1,m1) = E(expr, m0)
    in
        if DVtoBool(v1) then M(blk, m1) else M(blk2, m1)
    end
    
  | M ( itree(inode("WHILE_LOOP",_), [itree(inode("while",_), []), itree(inode("(",_), []), expr1, itree(inode(")",_), []), block1]), m0) =
    let
        fun N ( expr1, stmt1, m0) =
            let
                val (v, m1) = E(expr1, m0);
            in
                if DVtoBool(v) then N(expr1, stmt1, M(stmt1, m1))
                else m1
            end;
        val m2 = N(expr1, block1, m0);
    in
        m2
    end
    
 | M ( itree(inode("FOR_LOOP",_), [itree(inode("for",_), []), itree(inode("(",_), []), forInit, itree(inode(";",_), []), expr1, itree(inode(";",_), []), stmt1, itree(inode(")",_), []), block1  ]), m0) =
    let
        fun N ( stmt2, expr2, blk2, n0) =
            let
                val (v, n1) = E(expr1, n0);
                val n4 = if DVtoBool(v) then 
                    let
                        val n2 = M(blk2, n1);
                        val n3 = M(stmt2, n2);
                    in
                        N(stmt2, expr2, blk2, n3) 
                    end
                else n1
            in
                n4
            end
            
        val m1 = M(forInit, m0);
        val m2 = N(stmt1, expr1, block1, m1)
    in
        m2
    end
    
  | M ( itree(inode("FOR_INIT",_), [ asgnDec ]), m0) =
    let
        val m1 =  M(asgnDec, m0)
    in
        m1
    end
    
  | M ( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur");

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)









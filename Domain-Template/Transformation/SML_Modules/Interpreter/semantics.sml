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

fun E ( itree(inode("EXPRESSION",_), [disj1]), m0) = E(disj1, m0)
  | E ( itree(inode("DISJUNCTION",_), [equality1]), m0) = E(equality1, m0)
  | E ( itree(inode("EQUALITY",_), [relational1]), m0) = E(relational1, m0)
  | E ( itree(inode("boolean",_),[bool1]),m0) = if getLeaf(bool1) = "true" then (Boolean(true), m0) else (Boolean(false), m0)
  | E ( itree(inode("RELATIONAL",_),[additive1]),m0) = E(additive1, m0)
  | E ( itree(inode("ADDITIVE",_),[multiplicative1]),m0) = E(multiplicative1, m0)
  | E ( itree(inode("MULTIPLICATIVE",_),[exponential1]),m0) = E(exponential1, m0)
  | E ( itree(inode("EXPONENTIAL",_),[unary1]),m0) = E(unary1, m0)
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

  | E ( itree(inode("PRIMARY",_),[itree(inode("|",_),[]), expr1, itree(inode("|",_),[])]),m0) = 
    let
        val (v1, m1) = E(expr1, m0);
        val v2 = Integer(abs(DVtoInt(v1)));
    in
        (v2, m1)
    end
    
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
    
  | M ( itree(inode("STATEMENT_LIST",_), [ itree(inode("epsilon",_), []) ]), m0) = m0

  | M ( itree(inode("STATEMENT_LIST",_), [ stmt1, stmtlist1 ]), m0) =
    let
        val m1 = M(stmt1, m0);
        
        val m2 = M(stmtlist1, m1) 
    in
        m2
    end
    
  | M ( itree(inode("STATEMENT",_), [stmt1, itree(inode(";",_), [])]), m0) =
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
  | M ( itree(inode("BLOCK",_), [ itree(inode("{",_), []), stmtList, itree(inode("}",_), []) ]), m0) =
    let
        val m1 =  M(stmtList, m0)
    in
        m1 
    end

  | M ( itree(inode("PRINT_STATEMENT",_), [prnt, itree(inode("(",_), []), expr, itree(inode(")",_), []) ]), m0) =
    let
        val (v1,m1) = E(expr, m0)
        val p = print(DVtoString(v1));
    in
        m1
    end

 (* | M ( itree(inode("CONDITIONAL_STATEMENT",_), [itree(inode("if",_), []),itree(inode("(",_), []), expr, itree(inode(")",_), []), blk ]), m0) =
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
    end *)
    
    (* <FOR_LOOP>              ::= "for" "(" <FOR_INIT> ";" <EXPRESSION> ";" <ASSIGNMENT_STATEMENT> ")" <BLOCK>. *)
  | M ( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur");
  
(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)









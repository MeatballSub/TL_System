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
fun E ( itree(inode("EXPRESSION",_), [ disjunction ]), m0) =
    let
        val (v, m1) = E(disjunction, m0);
    in
        (v, m1)
    end
    
   | E ( itree(inode("EXPRESSION",_), [expr, itree(inode("or",_), []), disjunction]), m0) =
    let
        val v0 = false
        val (v1, m1) = E(expr, m0)
        val (v2, m2) = E(disjunction, m1)       
    in
        if v1 then (v1, m1) else if v2 then (v2, m2) else (v0, m0)
    end
    
   | E ( itree(inode("DISJUNCTION",_), [ equality ]), m0) =
    let
        val (v, m1) = E(equality, m0);
    in
        (v, m1)
    end
    
   | E ( itree(inode("DISJUNCTION",_), [disjunction, itree(inode("and", _),[]), equality]), m0) =
    let
        val v0 = false
        val (v1, m1) = E(disjunction, m0)
        val (v2, m2) = E(equality, m1)       
    in
        if v1 then if v2 then (true, m2) else (v0, m0) else (v0, m0)
    end
    
   | E ( itree(inode("EQUALITY",_), [ relational ]), m0) =
    let
        val (v, m1) = E(relational, m0);
    in
        (v, m1)
    end
    
   | E ( itree(inode("EQUALITY",_), [equality, itree(inode("==", _),[]), relational]), m0) =
    let
        val v0 = false
        val (v1, m1) = E(equality, m0)
        val (v2, m2) = E(relational, m1)       
    in
        if v1 = v2 then (true, m2) else (v0, m0)
    end
    
   | E ( itree(inode("EQUALITY",_), [equality, itree(inode("!=", _),[]), relational]), m0) =
    let
        val v0 = false
        val (v1, m1) = E(equality, m0)
        val (v2, m2) = E(relational, m1)       
    in
        if v1 = v2 then (v0, m0) else (true, m2)
    end
   | E ( itree(inode("boolean",_),[bool1]),m0) = if getLeaf(bool1) = true 
                                                 then ((Boolean)true, m0) 
                                                 else ((Boolean)false, m0) 
                                                 
   | E ( itree(inode("RELATIONAL",_), [ additive ]), m0) =
    let
        val (v, m1) = E(additive, m0);
    in
        (v, m1)
    end  
    
   | E ( itree(inode("RELATIONAL",_), [relational, itree(inode("<", _),[]), additive]), m0) =
    let
        val (v1, m1) = E(relational, m0)
        val (v2, m2) = E(additive, m1)       
    in
        if v1 < v2 then (true, m2) else (false, m0)
    end
    
   | E ( itree(inode("RELATIONAL",_), [relational, itree(inode(">", _),[]), additive]), m0) =
    let
        val (v1, m1) = E(relational, m0)
        val (v2, m2) = E(additive, m1)       
    in
        if v1 > v2 then (true, m2) else (false, m0)
    end
    
   | E ( itree(inode("RELATIONAL",_), [relational, itree(inode("<=", _),[]), additive]), m0) =
    let
        val (v1, m1) = E(relational, m0)
        val (v2, m2) = E(additive, m1)       
    in
        if v1 <= v2 then (true, m2) else (false, m0)
    end
    
   | E ( itree(inode("RELATIONAL",_), [relational, itree(inode(">=", _),[]), additive]), m0) =
    let
        val (v1, m1) = E(relational, m0)
        val (v2, m2) = E(additive, m1)       
    in
        if v1 >= v2 then (true, m2) else (false, m0)
    end
    
   | E ( itree(inode("ADDITIVE",_), [ multiplicative ]), m0) =
    let
        val (v, m1) = E(multiplicative, m0);
    in
        (v, m1)
    end  
    
   | E ( itree(inode("ADDITIVE",_), [additive, itree(inode("+", _),[]), multiplicative]), m0) =
    let
        val (v1, m1) = E(additive, m0)
        val (v2, m2) = E(multiplicative, m1)       
    in
        (v1 + v2, m2)
    end
    
   | E ( itree(inode("ADDITIVE",_), [additive, itree(inode("-", _),[]), multiplicative]), m0) =
    let
        val (v1, m1) = E(additive, m0)
        val (v2, m2) = E(multiplicative, m1)       
    in
        (v1 - v2, m2)
    end

   | E ( itree(inode("MULTIPLICATIVE",_), [ exponential ]), m0) =
    let
        val (v, m1) = E(exponential, m0);
    in
        (v, m1)
    end  
    
   | E ( itree(inode("MULTIPLICATIVE",_), [multiplicative, itree(inode("*", _),[]), exponential]), m0) =
    let
        val (v1, m1) = E(multiplicative, m0)
        val (v2, m2) = E(exponential, m1)       
    in
        (v1 * v2, m2)
    end
    
   | E ( itree(inode("MULTIPLICATIVE",_), [multiplicative, itree(inode("div", _),[]), exponential]), m0) =
    let
        val (v1, m1) = E(multiplicative, m0)
        val (v2, m2) = E(exponential, m1)       
    in
        (v1 / v2, m2)
    end
   | E ( itree(inode("MULTIPLICATIVE",_), [multiplicative, itree(inode("mod", _),[]), exponential]), m0) =
    let
        val (v1, m1) = E(multiplicative, m0)
        val (v2, m2) = E(exponential, m1)       
    in
        (v1 - v2, m2)
    end
(*

<MULTIPLICATIVE>        ::= <MULTIPLICATIVE> "*" <EXPONENTIAL>
                          | <MULTIPLICATIVE> "div" <EXPONENTIAL>
                          | <MULTIPLICATIVE> "mod" <EXPONENTIAL>
                          | <EXPONENTIAL>.

<EXPONENTIAL>           ::= <UNARY> "^" <EXPONENTIAL>
                          | <UNARY>.

<UNARY>                 ::= "-" <PRIMARY>
                          | "not" <PRIMARY>
                          | <PRIMARY>.

<PRIMARY>               ::= identifier
                          | integer
                          | "(" <EXPRESSION> ")"
                          | "|" <EXPRESSION> "|"
                          | <PREFIX_EXPRESSION>
                          | <POSTFIX_EXPRESSION>.  *)
                          
  | E ( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | E _ = raise Fail("error in Semantics.M - this should never occur"); 





fun M ( itree(inode("WFC_START",_), [ stmtlist1 ]), m0) = 
    let
        val m1 = M(stmtlist1, m0);
    in
        m1
    end
    
  | M ( itree(inode("STATEMENT_LIST",_), [ epsilon ]), m0) = m0

  | M ( itree(inode("STATEMENT_LIST",_), [ stmt1, stmtlist1 ]), m0) =
    let
        val m1 = M(stmt1, m0);
        val m2 = M(stmtlist1, m1);
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
        val p = showModel(m1);
    in
        m1
    end
 
   | M ( itree(inode("DECLARATION_STATEMENT",_), [ itree(inode("bool",_), []), id1 ]), m0) =
    let
        val m1 = updateEnvironment(getLeaf(id1), BOOL, new(m0), m0);
        val p = showModel(m1);
    in
        m1
    end
    
   | M ( itree(inode("DECLARATION_STATEMENT",_), [ itree(inode("int",_), []), id1, itree(inode("=", _), []), expr ]), m0) =
    let
        val m1 = updateEnvironment(getLeaf(id1), INT, new(m0), m0);
        val (v,m2) = E(expr, m1)
        val a_location = getLoc(accessEnv(getLeaf(id1), m2))
        val m3 = updateStore(a_location, v, m2)
        val p = showModel(m3);
    in
        m3
    end

   | M ( itree(inode("DECLARATION_STATEMENT",_), [ itree(inode("bool",_), []), id1, itree(inode("=", _), []), expr ]), m0) =
    let
        val m1 = updateEnvironment(getLeaf(id1), BOOL, new(m0), m0);
        val (v,m2) = E(expr, m1)
        val a_location = getLoc(accessEnv(getLeaf(id1), m2))
        val m3 = updateStore(a_location, v, m2)
        val p = showModel(m3);
    in
        m3
    end
    
    
 (*   <DECLARATION_STATEMENT> ::= int identifier
                          | bool ... *)


  | M ( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur");
  
(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)









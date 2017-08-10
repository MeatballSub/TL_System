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
*)


fun M( itree(inode("WFC_START",_), [ block1 ]), m0) = 
    let
        val m1 = M(block1, m0);
    in
        m1
    end
    
  | M( itree(inode("WFC_START",_), []), m0) = m0
  
  | M( itree(inode("BLOCK",_), [ itree(inode("{",_),[]), blockStatements1, itree(inode("}",_),[]) ]), (env0, loc0, s0)) =
    let
        val (env1, loc1, s1) = M(blockStatements1, (env0, loc0, s0));
        val m2 = (env0, loc0, s1);
    in
        m2
    end

  | M ( itree(inode("BLOCK_STATEMENTS",_), [ blockStatement1, blockStatements1 ]), m0) =
    let
        val m1 = M(blockStatement1, m0);
        val m2 = M(blockStatements1, m1);
    in
        m2
    end
    
  | M ( itree(inode("BLOCK_STATEMENT",_), [ blockStatement1 ]), m0) =
    let
        val m1 = M(blockStatement1, m0);
    in
        m1
    end
    
  | M ( itree(inode("DECLARATION_STMT",_),[type1, id]),m0) =
    let
        val m1 = updateEnvironment(id, INT, new(m0), m0)
    in
        m1
    end
  
  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)









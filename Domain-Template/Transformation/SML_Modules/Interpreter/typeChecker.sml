(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
    
*)
fun typeCheck( itree(inode("WFC_START",_), [ stmt_list ] ), m) = m


(*
fun typeCheck( itree(inode("WFC_START",_), [ BLOCK ] ), m0) =
        let
            val m1 = typeCheck(BLOCK, m0);
        in
            m1
        end
        
  | typeCheck( itree(inode("WFC_START",_), []), m) = m
  
  | typeCheck( itree(inode("BLOCK",_), [ itree(inode("{",_),[]) , BLOCK_STATEMENTS, itree(inode("}",_),[]) ]), m0) =
        let
            val m1 = typeCheck(BLOCK_STATEMENTS, m0);
        in
            m1
        end
        
  | typeCheck( itree(inode("BLOCK_STATEMENTS",_), [ blockStatement1, blockStatements1 ]), m0) =
    let
        val m1 = typeCheck(blockStatement1, m0);
        val m2 = typeCheck(blockStatements1, m1);
    in
        m2
    end

  | typeCheck ( itree(inode("BLOCK_STATEMENT",_), [ declarationStmt1:DECLARATION_STMT ]), m0) =
    let
        val m1 = typeCheck(declarationStmt1, m0);
    in
        m1
    end
    
  | typeCheck ( itree(inode("DECLARATION_STMT",_), [ type1, id1 ]), m0) =
    let
        val m1 = typeCheck(type1, m0);
        val m2 = typeCheck(id1, m1);
    in
        m2
    end
*)  
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)









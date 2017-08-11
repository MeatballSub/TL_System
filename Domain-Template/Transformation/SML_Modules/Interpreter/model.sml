(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list

exception runtime_error;
fun error msg = (print msg; raise runtime_error);

(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )

fun typeToString BOOL = "bool"
  | typeToString INT = "integer"
  | typeToString ERROR = "error";

fun DVtoString(Boolean value) = Bool.toString value
  | DVtoString(Integer value) = Int.toString value;

fun envEntryToString (id, t, loc) = "(" ^ id ^ "," ^ typeToString t ^ "," ^ Int.toString loc ^ ")";
fun storeEntryToString(loc, value) = "(" ^ Int.toString loc ^ "," ^ DVtoString(value) ^ ")";
(*
fun storeEntryToString(loc, value) = "(" ^ Int.toString loc ^ ")";
*)

fun showStore [] = print "\n\n"
  | showStore(s1::s) = (print("\n" ^ storeEntryToString s1); showStore s);

fun showEnv [] = print "\n\n"
  | showEnv(e1::e) = (print("\n" ^ envEntryToString e1); showEnv e);

fun showLoc(l:loc) = print("Location = " ^ Int.toString l ^ "\n\n");

fun showModel(e:env, l:loc, s:store) =
    let
        val e1 = showEnv(e)
        val l1 = showLoc(l);
        val s1 = showStore(s);

    in
        (e, l, s)
    end
;

fun new(e:env, loc1:loc, s:store) = loc1 + 1;

fun updateEnvironment(id, a_type, a_loc, (e:env, location:loc, s:store)) =
    let
        fun aux(id, a_type, a_loc, []) = [(id, a_type, a_loc)]
          | aux (id, a_type, a_loc, (id1, type1, loc1)::e) =
                if id=id1 then
                    (id1, a_type, a_loc)::e
                else
                    (id1, type1, loc1)::aux(id, a_type, a_loc, e);
        fun aux2(id, l, []) = l + 1
          | aux2(id, l, (id1, type1, loc1)::e) =
                if id=id1 then
                    l
                else
                    aux2(id, l, e);
    in
        (aux(id, a_type, a_loc, e), aux2(id, location, e), s)
    end
;

fun updateStore(a_loc, a_value, (e:env, location:loc, s:store)) = 
    let
        fun aux (loc, value, []) = [(loc, value)]
          | aux (loc, value, (loc1, value1)::s) =
                if loc=loc1 then
                    (loc, value)::s
                else
                    (loc1, value1)::aux(loc, value, s);
    in
        (e, location, aux(a_loc, a_value, s))
    end
;

fun accessEnv (id1, (env, location, s)) =
    let
        val msg = "Error: accessEnv " ^ id1 ^ " not found.";
        fun aux [] = error msg
          | aux ((id,t,loc)::env) = if id1=id then (t, loc)
                                              else aux env;
    in
        aux env
    end
;

fun accessStore (loc1, (env, location, s)) =
    let
        val msg = "Error: accessStore " ^ loc1 ^ " not found.";
        fun aux [] = error msg
          | aux ((loc,dv)::s) = if loc1=loc then dv
                                            else aux s;
    in
        aux s
    end
;

fun getLoc(a_type, a_loc)  = a_loc;
fun getType(a_type, a_loc) = a_type;


(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)













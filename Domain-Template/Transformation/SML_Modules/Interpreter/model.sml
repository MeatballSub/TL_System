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

fun new(env, loc, store) = (env, loc + 1, store);

fun updateEnvironment(id, a_type, a_loc, (env, location, s)) =
    let
        fun aux(id, a_type, a_loc, []) = [(id, a_type, a_loc)]
          | aux (id, a_type, a_loc, (id1, type1, loc1)::env) =
                if id=id1 then
                    (id, a_type, a_loc)::env
                else
                    (id1, type1, loc1)::aux(id, a_type, a_loc, env);
    in
        aux(id, a_type, a_loc, env)
    end
;

fun updateStore(a_loc, a_value, (env, location, s)) = 
    let
        fun aux (loc, value, []) = [(loc, value)]
          | aux (loc, value, (loc1, value1)::s) =
                if loc=loc1 then
                    (loc, value)::s
                else
                    (loc1, value1)::aux(loc, value, s);
    in
        aux(a_loc, a_value, s)
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













(** Unification over generic first order terms *)

open Printf
open Terms

(* Unification variables are integers. *)    
type variable = int

(* First order term, polymorphic w.r.t. its constructor. *) 
type 'cons pterm = ('cons, variable) Terms.t

(* Exception raised on unification error *)
exception Mismatch of string

(* Environment with unification variables as key type. *)
module VarMap = ExtMap.Make(
  struct
    type t = variable
    let compare : variable -> variable -> int = Pervasives.compare
  end)

let extend_var env key elt =
  VarMap.add key elt env

let lookup_var map key =  VarMap.find key map

let string_of_variable = string_of_int

(* ------------------------------------------------------------------------- *)

type freshgen = variable Utils.FreshGen.acc

(* ------------------------------------------------------------------------- *)

(* The first order terms are labelled according to this module.
   We allow the terms to be enriched with some debugging information (as a string), 
   to make the type errors clearer.  *)
(* module type TermSig =
 * sig
 * 
 *   type constructor_label
 *   type term = constructor_label pterm
 * 
 *   val label_compatible : constructor_label -> constructor_label -> bool
 *   val string_of_label : constructor_label -> string
 *   val debug_of_label : constructor_label -> string
 * 
 * end *)

module Make(P : Types.S with type var = int)
=
struct

  type term = P.t

  (* ------------------------------------------------------------------------- *)

  (* A term printer. *)

  let print out_chan t =
    let s = P.print t in
    fprintf out_chan "%s\n" s 

  (* ------------------------------------------------------------------------- *)

  (* A substitution maps variables to terms. *)

  type substitution =
    term VarMap.t

  type equations =
    (term * term) list

  (* ------------------------------------------------------------------------- *)

  (* This is the union-find module dedicated to type unification. *)

  (* Coerce the type of our union-find structure.
     The first parameter is the type of the elements being unified.
     The second is the accumulator, here composed of a list of equations
     (generated during the unification process, cf [merge]) and an accumulator,
     specified by the input P module. *)
  type uf = (term option, equations) UnionFind.t

  (* ------------------------------------------------------------------------- *)

  (* [Build] helps construct unification problems. *)

  module Build = struct

    type build_env = {
      equations     : equations;
      type_freshgen : freshgen;
    }

    let initial_build_env = {
      equations = [];
      type_freshgen  = Utils.FreshGen.initial 0 succ;
    }

    (* returns a fresh variable boxed in a term *)
    let fresh env =
      let acc, tv = Utils.FreshGen.fresh env.type_freshgen in
      let t = TermVar tv in
      { env with 
        type_freshgen = acc }, t

    (* stores a new equation *)
    let join env t1 t2 =
      { env with equations = (t1, t2) :: env.equations }

  end

  (* ------------------------------------------------------------------------- *)

  (* [merge t1 t2 acc] merges two representatives, during _type_ unification *)
  let merge =
    fun repr1 repr2 equations ->
      match repr1, repr2 with
      | None, x
      | x, None -> 
        x, equations
      | Some t0, Some t1 ->
        repr1, (t0, t1) :: equations

  let unify (state : Build.build_env) =
    let uf = UnionFind.make merge in
    let uf =
      List.fold_left (fun uf_state var ->
          UnionFind.mkroot None var uf_state
        ) uf (Utils.FreshGen.variables state.Build.type_freshgen) 
    in
    let rec unify (union_find : uf) =
      function
      | [] -> union_find
      | (t1, t2) :: eqs ->
        (* (useful debugging code) *)
        (* let prtyp x = string_of_term_plain string_of_int string_of_label x in *)
        (* let s = Printf.sprintf "uniying %s to %s." (prtyp t1) (prtyp t2) in *)
        (* let _ = Utils.serr s in *)
        (match t1, t2 with
         | TermVar v1, TermVar v2 ->
           let uf, eqs = UnionFind.union v1 v2 union_find eqs in
           unify uf eqs
         | TermVar v, term2
         | term2, TermVar v ->
           let r_key, uf  = UnionFind.repr v union_find in
           let v_repr     = UnionFind.get r_key uf in
           let repr, eqs  = merge v_repr (Some term2) eqs in
           let union_find = UnionFind.set r_key repr uf in
           unify union_find eqs
         | TermCons((tc1, debug1), ts1), TermCons((tc2, debug2), ts2) ->
           let l1 = List.length ts1 in
           let l2 = List.length ts2 in
           if not (Types.typecons_equal tc1 tc2) || (l1 <> l2) then
             let _ = 
               fprintf stderr 
                 "term %s incompatible with term %s\n"
                 (P.print t1)
                 (P.print t2)
             in
             raise (Mismatch (sprintf "Unification error"))
           else
             unify union_find (List.combine ts1 ts2 @ eqs))
    in
    unify uf state.Build.equations

  (* ------------------------------------------------------------------------- *)

  (* The read back phase turns the state of the union-find algorithm
     back into a most general unifier, that is, a mapping of variables
     to terms. This is essentially a graph traversal process,
     implemented using depth-first search. An acyclicity check is
     performed on the fly. *)

  exception OccurCheck (* Raised whenever we encouter a cycle in a type. *)

  let read_back (env : Build.build_env) (state : uf) : substitution =
    (* This code is from the programming project for MPRI's course 2.4.2,
       credits to X. Leroy or F. Pottier (I think). 
       Slightly adapted to our setting. *)
    let rec dfs visited uf_state node =
      if List.mem node visited then
        raise OccurCheck
      else
        let node, uf_state = UnionFind.repr node uf_state in
        let repr           = UnionFind.get node uf_state in
        begin match repr with
          | None -> (* Case of incomplete unification. *)
            TermVar node
          | Some t ->
            term_lift
              (fun x -> x)
              (fun v -> dfs (node :: visited) uf_state v)
              t
        end
    in
    let map = 
      List.fold_left begin fun map v ->
        let t = dfs [] state v in
        VarMap.add v t map
      end VarMap.empty (Utils.FreshGen.variables env.Build.type_freshgen)
    in
    map

  let instantiate_term (s : substitution) (t : term) =
    term_lift
      (fun x -> x)
      (fun x -> 
         try VarMap.find x s
         with Not_found -> TermVar x)
      t

end




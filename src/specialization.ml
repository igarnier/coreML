(* Data type specialization. Assumes that alpha-conversion and monomorphisation are done. *)

(*i*)
open Printf
(*i*)

exception Specialization_error of string

let spec_err x = raise (Specialization_error x)

(* The data type specialization must rebuild non-parameterized 
   data type declarations. For instance, if the user uses polymorphic
   lists with types $\tau_1 \ldots \tau_n$, then this module will
   produces $n$ specialized instances of the $list$ declaration
   - one for each domain type $\tau_i$. Since we can't overload
   data constructors, we must specialize them too. Specialization
   is the counterpart on type declarations of monomorphisation.

   We proceed by structural induction on the \textbf{monomorphised} program. 
   We collect the different usages of each polymorphic type (at \textit{Econstruct}
   expressions). We also rename data constructors. We store all this data 
   as a mapping from old constructors and domain types to codomain types and
   fresh constructors.

   After collecting the data, we modify the type declarations accordingly.
   The module is defined as a functor parameterized by a typing function
   [id_typing] and a fresh variable generator [freshgen].
*)

module type InputSig =
sig
  val id_typing  : Ast.unique_id -> Types.NoDebug.term
  val freshgen : Fresh.t
end

module Make(I : InputSig) =
struct

  open Ast
  open Terms
  open Utils
    
  let typing (_, id) = I.id_typing id

  let builtin_types =
    [ "->"; "*"; "int"; "float"; "string" ]

  (* [TypeSet] is an auxilliary module which stores the information
     about data constructor types usage. This information is a triple
     made of a domain type, a codomain type and a fresh constructor.
     We refer to this kind of triple as "instance".
     TypeSet.t's are quotiented by alpha-equivalence. *)
  module TypeSet =
  struct
    
    type domain_type   = Types.NoDebug.term option
    type codomain_type = Types.NoDebug.term
    type fresh_name    = string
	
    let rec domain_types_equal : domain_type -> domain_type -> bool =
      fun t1 t2 ->
	match (t1, t2) with
	  | None, None -> true
	  | Some t1', Some t2' ->
	      Types.NoDebug.types_equivalent t1' t2'
	  | _ -> false

    include Set.Make(
      struct
	
	type t = domain_type * codomain_type * fresh_name
	    
	let compare (l1,cod1,_) (l2,cod2,_) =
	  if domain_types_equal l1 l2 then
	    if Types.NoDebug.types_equivalent cod1 cod2 then
	      0
	    else
	      Pervasives.compare cod1 cod2
	  else
	    Pervasives.compare l1 l2
	    
      end)
  end

  (* [SpecEnv] maps constructors to a set of instances ([consmap] field). It also maps typenames
     and usages to fresh typenames ([typemap] field).
     An instance of a constructor is a triple (domain, codomain, fresh).
     An usage is a tuple of parameter types for a polymorphic type.
     Let's consider a type "type t ('a,'b) = Foo of 'a * 'b".
     When encoutering in the source some constructors Foo(3,2.0) and Foo("bar","baz"),
     the SpecEnv will associate "Foo" to the set containing  ((int*float),(int,float) t,"Foo0")
     and ([string*string],(string,string) t,"Foo1").
     We will also map ("t", (int * float)) to e.g. "t0" and  ("t", (string * string)) to "t1".
     There is indeed some redundant information, but this allow us to simplify some parts of
     the code. *)
  module SpecEnv =
  struct

    module TypeMap = Types.AlphaTypeMap(Types.NoDebug)

    type t = 
	{ consmap : TypeSet.t StringMap.t;
	  typemap : (string TypeMap.t) StringMap.t }

    let lookup key map =
      StringMap.find_opt key map.consmap

    let mem key map = 
      StringMap.mem key map.consmap

    let search default key map = 
      StringMap.search default key map.consmap

    let add key elt map = 
      { map with consmap = StringMap.add key elt map.consmap }

    (*i-----------------------i*)

    let find_new_typename typename args map =
      let tmap = match StringMap.find_opt typename map.typemap with
	| None ->
	    spec_err (sprintf "No new typename for type [%s] - bug found" typename)
	| Some tmap -> tmap
      in
      let t = TermCons("*", args) in
	match TypeMap.find_opt t tmap with
	  | None ->
	      spec_err (sprintf "No instances found for type [%s] - bug found" typename)
	  | Some res -> 
	      TermCons(res, [])

    let add_type_instance orig_typename param_types new_typename map =
      (* Pack the parameters in a tuple. *)
      let param_types = TermCons("*", param_types) in
      let typemap =
	match StringMap.find_opt orig_typename map.typemap with
	  | None -> TypeMap.empty
	  | Some x -> x
      in
      let typemap = TypeMap.add param_types new_typename typemap in
	{ map with 
	  typemap = StringMap.add orig_typename typemap map.typemap }

  end

  module Mapping =
  struct
    
    type t = SpecEnv.t * Fresh.t

  end


  (* Transforms a type (for instance the type of a variant constructor)
   * into its specialized representation. We proceed by recursing on
   * the type. *)
  let rec specialize_type env typ =
    match typ with
      | TermVar _ ->
	  failwith "Specialization.specialize_datatypes/spec : type not ground"
      | TermCons("->", [dom; codom]) ->
	  TermCons("->", [specialize_type env dom; specialize_type env codom])
      | TermCons("*", fields) ->
	  TermCons("*", List.map (specialize_type env) fields)
      | TermCons(cons, subterms) ->
	  if List.mem cons builtin_types then
	    TermCons(cons, List.map (specialize_type env) subterms)
	  else
	    SpecEnv.find_new_typename cons subterms env
	      


  (* [find cons typ cod env] associates to {a constructor or a field [cons], a domain
   * type [typ], the type of the whole expression [cod] and an environment}, a 
   * specialized constructor or field. *)
  let find : string -> TypeSet.domain_type -> TypeSet.codomain_type -> SpecEnv.t -> string option =
    fun name typ cod env ->
      match SpecEnv.lookup name env with
	| Some instances ->
	    let matching_instances = TypeSet.filter (fun (t, codomain, _) ->
	      (TypeSet.domain_types_equal typ t)
	      && (Types.NoDebug.types_equivalent cod codomain)
	    ) instances in
	      (match TypeSet.elements matching_instances with
		| [] -> None
		| [_,_,ident] -> Some ident
		| _ ->
		    let s = "Specialization.specialize_datatypes/find : more than one matching instance for a given type." in
		      spec_err s)
	| None -> None

  (* [add_mapping cons dom codom env] updates the environment [env] with a new instance for the
   * given constructor/field [name] and types [dom] and [codom].
   * If this specialized constructor already exists, it is readily returned. If not, it
   * is created and the environment is updated accordingly. *)
  let add_mapping : 
      string -> TypeSet.domain_type -> TypeSet.codomain_type -> Mapping.t -> string * Mapping.t =
    fun name domtype codtype (env, gen) ->
      match find name domtype codtype env with
	| Some fresh_name ->
	    (fresh_name, (env, gen))
	| None ->
	    let gen, fresh   = Fresh.next gen in
	    let fresh_constr = name^"_"^(Fresh.var fresh) in
	    let set = SpecEnv.search TypeSet.empty name env in
	    let set = TypeSet.add (domtype, codtype, fresh_constr) set in
	    let env = SpecEnv.add name set env in
	      (fresh_constr, (env, gen))

  let codomains_of_decl mapping decl =
    let (env, _) = mapping in
      match decl.tdecl_kind with
	| SumType intro_rules ->
	    let cons = constructors_of_inductive_def intro_rules in
	      (* Gather all usages of every constructor. *)
	    let cons_type_infos = List.fold_left (fun usages (cons, _) ->
	      match SpecEnv.lookup cons env with
		| Some res ->
		    TypeSet.union usages res
		| None -> 
		    usages
	    ) TypeSet.empty cons in
	    let cons_type_infos = TypeSet.elements cons_type_infos in
	    let codomains = List.map proj_2 cons_type_infos in
	      codomains
	| Builtin ->
	    (* [] *)
	    failwith "specialization error : not an inductive type"
	      

  let specialize_decl mapping mutual_decls =

    let (env, freshgen) = mapping in
      
    let rec specialize_aux typedecl =
      match typedecl with
	| [] -> []
	| decl :: l ->
	    let decls = match decl.tdecl_kind with
	      | SumType intro_rules ->
		  
		  let cons = constructors_of_inductive_def intro_rules in

		  (* Gather all usages of each constructor. *)
		  let instances = List.fold_left (fun acc (constr, _) ->
		    match SpecEnv.lookup constr env with
		      | Some res ->
			  TypeSet.union acc res
		      | None ->
			  acc (* Unused data constructor ... suppress it 
			       * from the declaration. *)
		  ) TypeSet.empty cons in
		    
		  (* Sort the usages of the constructors by codomain. *)
		  let instances = Utils.classify 
		    (fun (_,codom1,_) (_,codom2,_) -> 
		      Types.NoDebug.types_equivalent codom1 codom2)
		    (TypeSet.elements instances)
		  in

		  (* We must update the domain of each constructor according to the new
		     mapping. *)		    
		  let instances = List.map (fun instance ->
		    
		    let codomain = proj_2 (List.hd instance) in
		    let new_codomain = match codomain with
		      | TermCons(head, parameters) ->
			  SpecEnv.find_new_typename head parameters env
		      | TermVar _ ->
			  spec_err "In type specialization : type has a bogus variable codomain"
		    in
		    let new_typename = Utils.no_some (Types.label_of_type new_codomain) in
		    let instance = List.map (fun (dom, _, fresh_cons) ->
		      let dom = Utils.opt_map (specialize_type env) dom in
			(dom, fresh_cons)
		    ) instance in
		      
		      (new_typename, instance)
			
		  ) instances in

		  (* Now, we must convert back these into the Ast.* format. *)
		  let kinds = List.fold_left (fun kinds (tname, instance) ->

		    let constructors = List.map (fun (dom, freshconstr) ->
		      let contents = dom in
			(freshconstr, contents)
		    ) instance in
		      (tname, (SumType (IndIntros constructors))) :: kinds
		  ) [] instances in

		  let decls = List.map (fun (tname, kind) ->
		    { tdecl_name = tname;
		      tdecl_kind = kind }
		  ) kinds in

		    decls
		      
	      | Builtin ->
		  [decl]

	    in
	    let decls' = specialize_aux l in
	      List.rev_append decls decls'
    in
      (env, freshgen), specialize_aux mutual_decls

  (* [specialize_pattern env patt] updates constructor and record patterns
   * according to the mapping provided in [env]. This relies on the assumption
   * that patterns are well-typed. *)
  let rec specialize_pattern mapping (patt_desc, patt_id) =
    let patt_type = I.id_typing patt_id in
    let desc, mapping = match patt_desc with
      | Pany
      | Pvar _
      | Pconst _ ->
	  patt_desc, mapping
      | Ptuple patterns ->
	  let patts, mapping = List.fold_right (fun patt (patterns, mapping) ->
	    let patt, mapping = specialize_pattern mapping patt in
	      (patt :: patterns), mapping
	  ) patterns ([], mapping) in
	    (Ptuple patts), mapping
      | Pconstruct(cons, None) ->
	  let cons', mapping = add_mapping cons None patt_type mapping in
	    (Pconstruct(cons', None)), mapping
	      
      | Pconstruct(cons, Some patt) ->
	  let cons', mapping = add_mapping cons (Some (typing patt)) patt_type mapping in
	  let patt, mapping  = specialize_pattern mapping patt in
	    (Pconstruct(cons', Some patt)), mapping
    in
      (desc, patt_id), mapping

	
  (* [scan_for_usages] and [scan_for_usages_expr] do the bulk of the work. They scan
   * the program, looking for usages of data constructors. Encoutering
   * one of them, they look in [mapping] wether some previous usage of the same constructor/field
   * with the same type (up to alpha-conversion) exists. In this case, the constructor/field is 
   * replaced with its
   * specialized instance. In the other case, a fresh constructor/field is produced and
   * the old (constructor/field, type) is mapped to the fresh one. 
   * Not tail recursive, will it blow up the stack ? *)
  let rec scan_for_usages (mapping : Mapping.t) (decls, main) =
    let main, mapping = scan_for_usages_expr mapping main in
      ((decls, main), mapping)

  and scan_for_usages_expr mapping expr =
    let (expr_desc, expr_id) = expr in
    let expr_type = typing expr in
      match expr_desc with
	| Eident _
	| Econstant _ ->
	    expr, mapping

	| Elet(vv, bound, body) ->
	    let bound, mapping = scan_for_usages_expr mapping bound in
	    let body,  mapping = scan_for_usages_expr mapping body in
	      (Elet(vv, bound, body), expr_id), mapping
		
	| Efunction(vv, body) ->
	    let body,  mapping = scan_for_usages_expr mapping body in
	      (Efunction(vv, body), expr_id), mapping

	| Efixpoint(fixv, vv, body) ->
	    let body,  mapping = scan_for_usages_expr mapping body in
	      (Efixpoint(fixv, vv, body), expr_id), mapping

	| Eapply(func, args) ->
	    let func, mapping = scan_for_usages_expr mapping func in
	    let args, mapping =
	      List.fold_right (fun e (args, mapping) ->
		let arg, mapping = scan_for_usages_expr mapping e in
		  (arg :: args, mapping)
	      ) args ([], mapping)
	    in
	      (Eapply(func, args), expr_id), mapping
		
	| Ematch(matched_expr, matching) ->
	    let matched, mapping = scan_for_usages_expr mapping matched_expr in
	    let matching, mapping = 
	      List.fold_right (fun (patt, e) (matching, mapping) ->
		let expr, mapping = scan_for_usages_expr mapping e in
		let patt, mapping = specialize_pattern mapping patt in
		  (patt, expr) :: matching, mapping
	      ) matching ([],mapping) in
	      (Ematch(matched, matching), expr_id), mapping

	| Etuple fields ->
	    let fields, mapping = 
	      List.fold_right (fun e (fields, mapping) ->
		let e, mapping = scan_for_usages_expr mapping e in
		  (e :: fields, mapping)
	      ) fields ([], mapping) in
	      (Etuple fields, expr_id), mapping

	| Econstruct(constr, None) ->
	    let fresh, mapping  = add_mapping constr None expr_type mapping in
	      (Econstruct(fresh, None), expr_id), mapping

	| Econstruct(constr, Some e) ->
	    let t          = typing e in
	    let e, mapping = scan_for_usages_expr mapping e in
	    let fresh, mapping = add_mapping constr (Some t) expr_type mapping in
	      (Econstruct(fresh, Some e), expr_id), mapping
		

  let topological_sort structures =
    (* 1) Extract all the type declarations. *)
    let typedecls, not_typedecls = List.fold_right (fun si (tdecls, not_tdecls) ->
      match si with
        | (Itypedecl decls, _) ->
	    (si :: tdecls, not_tdecls)
        | _ -> (tdecls, si :: not_tdecls)
    ) structures ([], []) in

    (* 2) extract from a typedecl all the types it references
     * 2.a) extract from a core type all the non-builtin types it 
     * references *)
    let rec core_type_refs acc typ =
      match typ with
	| TermCons(cons, list) ->
	    if List.mem cons builtin_types then
	      core_type_refs_list acc list
	    else
	      core_type_refs_list (cons :: acc) list
	| _ -> acc
    and core_type_refs_list acc list =
      List.fold_left core_type_refs acc list
    in
      (* 2.b) extract the references from a type declaration *)
    let typedecl_references acc decl =
      match decl with
	| SumType intro_rules ->
	    let cons = constructors_of_inductive_def intro_rules in
	    List.fold_left (fun acc (_, consdom) ->
	      match consdom with
		| None -> acc
		| Some typ ->
		    core_type_refs acc typ
	    ) acc cons
	| Builtin ->
	    acc
    in
      (* 2.c) extract the references from a list of type declarations. *)
    let decls_references acc decls =
      List.fold_left (fun acc typedecl ->
	typedecl_references acc typedecl
      ) acc decls
    in

    (* 3) Establish a comparison function between typedecls. *)
    let compare (decl1, _) (decl2, _) =
      match decl1, decl2 with
	| (Itypedecl decls1), (Itypedecl decls2) ->
	    let tnames1, decls1 = List.split (List.map (fun d -> d.tdecl_name, d.tdecl_kind) decls1) in
	    let tnames2, decls2 = List.split (List.map (fun d -> d.tdecl_name, d.tdecl_kind) decls2) in
	    let refs1 = decls_references [] decls1 in
	    let refs2 = decls_references [] decls2 in
	    let c1before2   = List.exists (fun tn2 -> List.mem tn2 tnames1) refs2 in
	    let c2before1   = List.exists (fun tn1 -> List.mem tn1 tnames2) refs1 in
	      if c1before2 && c2before1 then
		spec_err "Bug found in the topological sort : mutually recursive typedecls"
	      else if c1before2 then
		-1
	      else
		1
	| _ ->
	    spec_err "Bug found in the topological sort"
    in
      (List.sort compare typedecls) @ not_typedecls
	
	

  let perform_specialization (decls, main) =
    let init_env = { SpecEnv.consmap = StringMap.empty;
                     SpecEnv.typemap = StringMap.empty } in
    let init_gen = I.freshgen in
    let init_mapping = (init_env, init_gen) in
    let (decls, main), mapping = scan_for_usages init_mapping (decls, main) in

    let inductive, builtin = 
      List.partition
	(function
	  | (Itypedecl _, _) -> true
	  | _ -> false
	) decls 
    in
    let ind_decls = List.map (function 
	(Itypedecl decls, _) -> decls
      |_ -> failwith "bug found") inductive in
    let all_decls = List.fold_left List.rev_append [] ind_decls in
    let instances = List.map (codomains_of_decl mapping) all_decls in
    let instances = List.fold_left List.rev_append [] instances in
      (* Classify by codomain. *)
    let instances = Utils.classify Types.NoDebug.types_equivalent instances in
      (* Pick a representative by equivalence class *)
    let instances = List.map List.hd instances in

    (* Create a fresh typename for each codomain *)
    let mapping = List.fold_left (fun (env, freshgen) codom ->
      match codom with
	| TermCons(typename, []) ->
	    (* No type parameters. Add the type as is. *)
	    let env = SpecEnv.add_type_instance typename [] typename env in
	      (env, freshgen)
	| TermCons(typename, type_args) ->
	    let gen, fresh = Fresh.next freshgen in
	    let freshname  = typename^"_"^(Fresh.var fresh) in
	    let env = SpecEnv.add_type_instance typename type_args freshname env in
	      (env, gen)
	| TermVar _ ->
	    spec_err "In type specialization : type has a bogus variable codomain"
    ) mapping instances in

    let mapping, all_decls = specialize_decl mapping all_decls in
    let decls = builtin @ [(Itypedecl all_decls, 0)] in

(*     let decls, mapping = List.fold_left (fun (items, mapping) si -> *)
(*       let (si_desc, si_id) = si in *)
(* 	match si_desc with *)
(* 	  | Itypedecl decls -> *)
(* 	      let mapping, decls = specialize_decl mapping decls in *)
(* 		(match decls with *)
(* 		  | [] -> *)
(* 		      (si :: items, mapping) *)
(* 		  | _ -> *)
(* 		      let result = (Itypedecl decls, si_id) in *)
(* 			(result :: items, mapping)) *)
(* 	  | _ -> *)
(* 	      (si :: items, mapping) *)
(*     ) ([], mapping) decls in *)
(*     let decls = topological_sort decls in *)
      (decls, main)

end

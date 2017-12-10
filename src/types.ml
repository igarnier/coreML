(* Types *)

(*  This modules defines our types, wich are in fact simple 
    first-order terms with some distinguished constructors
    (tuple, arrow \ldots). *)

open Batteries
open Printf

(* type constructor *)
type typecons =
  | TArrow
  | TProduct
  | TString
  | TFloat
  | TInt
  | TChar
  | TBool
  | TUnit
  | TUserDefined of string

(* type 'a parsed = (typecons, string) Terms.t *)

(* type constructor equality *)

let typecons_equal (tc1 : typecons) (tc2 : typecons) =
  tc1 = tc2

let typecons_compare (tc1 : typecons) (tc2 : typecons) =
  Pervasives.compare tc1 tc2

(* Printing types *)

let print_typecons = function
  | TArrow   -> "->"
  | TProduct -> "*"
  | TString  -> "string"
  | TFloat   -> "float"
  | TInt     -> "int"
  | TChar    -> "char"
  | TBool    -> "bool"
  | TUnit    -> "unit"
  | TUserDefined s -> s

module type ParamS =
  sig
    type debug
    type var

    val default     : debug
    val print_debug : debug -> string option
    val print_var   : var -> string
  end

module type S =
sig
  type debug
  type var
  type t = (typecons * debug, var) Terms.t

  val set_debug : debug -> t -> t

  val print : t -> string
  val compare : t -> t -> int
  val alpha_equivalent : t -> t -> bool
    
  val free_variables : t -> var list
  val is_ground : t -> bool
  val subst : t -> var -> t -> t
  val head : t -> typecons option

  val make : ?debug:debug -> typecons -> t list -> t
  val make_userdef : ?debug:debug -> string -> t list -> t

  module Predefined :
    sig
      val arrow  : ?debug:debug -> t -> t -> t
      val tuple  : ?debug:debug -> t list -> t
      val string : ?debug:debug -> unit -> t
      val float  : ?debug:debug -> unit -> t
      val int    : ?debug:debug -> unit -> t
      val char   : ?debug:debug -> unit -> t
      val bool   : ?debug:debug -> unit -> t
      val unit   : ?debug:debug -> unit -> t
    end

end

module Make :
  functor (P : ParamS) -> S with type debug = P.debug and type var = P.var = 
  functor (P : ParamS) ->
  struct

    type debug = P.debug
    type var   = P.var
    type t = (typecons * debug, var) Terms.t

    let set_debug debug typ =
      match typ with
      | Terms.TermVar _ -> typ
      | Terms.TermCons((cons, _), subterms) ->
        Terms.TermCons((cons, debug), subterms)

    let rec print (typ : t) =
      match typ with
      | Terms.TermVar v -> P.print_var v
      | Terms.TermCons((typecons, debug), fields) ->
        let fields = List.map print fields in
        let type_s =
          match typecons, fields with
          | TArrow, [ lhs; rhs ] ->
            Printf.sprintf "(%s %s %s)" lhs (print_typecons typecons) rhs
          | TArrow, _ ->
            invalid_arg "arrow type must have arity two"
          | TProduct, fields ->
            "("^(Utils.print_list " * " (fun x -> x) fields)^")"
          | _, [] ->
            print_typecons typecons
          | _, _ ->
            let fields = Utils.print_list ", " (fun x -> x) fields in
            (print_typecons typecons)^"("^fields^")"
        in
        match P.print_debug debug with
        | None -> type_s
        | Some debug_s ->
          type_s^"["^debug_s^"]"

    (* alpha-equivalence *)
    let rec alpha_convert_type mapping seed (typ : t) =
      match typ with
      | Terms.TermVar v ->
        if List.mem_assoc v mapping then
          (Terms.TermVar (List.assoc v mapping), mapping, seed)
        else
          let next = seed+1 in
          (Terms.TermVar seed, (v, next) :: mapping, next)
      | Terms.TermCons(x, subterms) ->
        let subterms, mapping, seed = List.fold_left (fun (subterms, mapping, seed) term ->
            let term, mapping, seed = alpha_convert_type mapping seed term in
            (term :: subterms, mapping, seed)
          ) ([], mapping, seed) subterms in
        (Terms.TermCons(x, List.rev subterms), mapping, seed)

    let rec compare_alpha t1 t2 =
      match (t1, t2) with
      | Terms.TermVar v1, Terms.TermVar v2 -> v1 = v2
      | Terms.TermCons(x1, subterms1), Terms.TermCons(x2, subterms2) ->
        if List.length subterms1 = List.length subterms2 then
          (typecons_equal (fst x1) (fst x2)) &&
          (List.for_all2 compare_alpha subterms1 subterms2)
        else
          false
      | _ -> false

    let compare t1 t2 =
      let (t1, _, _) = alpha_convert_type [] 0 t1 in
      let (t2, _, _) = alpha_convert_type [] 0 t2 in
      Pervasives.compare t1 t2

    let alpha_equivalent t1 t2 =
      compare t1 t2 = 0

    (* Some operations on type & type variables *)

    (* Peforms a 'fold' on the type structure. *)
    let rec fold fv fc (typ : t) =
      match typ with
      | Terms.TermVar x -> fv x
      | Terms.TermCons(cons, subtrees) ->
        let sub' = List.map (fold fv fc) subtrees in
        fc cons sub'

    (* Returns a list of all free type variables in [typ].
       (Since there is no explicit quantification, all variables are 'free' ...) *)
    let free_variables typ =
      fold 
        (fun v -> [v])
        (fun _ subterms -> List.flatten subterms)
        typ

    (* A type is ground if it contains no variables. *)
    let rec is_ground =
      function
      | Terms.TermCons(_, subterms) ->
        List.for_all is_ground subterms
      | Terms.TermVar _ -> false

    (* Instantiates a type variable for a (possibly non-ground) type in [typ] *)
    let rec subst typ v new_typ =
      match typ with
      | Terms.TermCons(x, subterms) ->
        let subterms = List.map (fun subtyp -> 
            subst subtyp v new_typ
          ) subterms
        in
        Terms.TermCons(x, subterms)
      | Terms.TermVar v' ->
        if v = v' then
          new_typ
        else
          typ 

    let head (typ : t) =
      match typ with
      | Terms.TermVar _      -> None
      | Terms.TermCons(x, _) -> Some (fst x)


    let make ?(debug=P.default) typecons subterms =
      Terms.TermCons((typecons, debug), subterms)

    let make_userdef ?(debug=P.default) typename subterms =
      Terms.TermCons((TUserDefined typename, debug), subterms)


  module Predefined =
    struct

      let mk0ary debug head =
        Terms.TermCons((head, debug), [])

      let arrow ?(debug=P.default) dom codom = 
        make ~debug TArrow [dom; codom]

      let tuple ?(debug=P.default) terms =
        make ~debug TProduct terms

      let string ?(debug=P.default) () =
        mk0ary debug TString

      let float ?(debug=P.default) () =
        mk0ary debug TFloat

      let int ?(debug=P.default) () =
        mk0ary debug TInt

      let char ?(debug=P.default) () =
        mk0ary debug TChar

      let bool ?(debug=P.default) () =
        mk0ary debug TBool

      let unit ?(debug=P.default) () =
        mk0ary debug TUnit

    end

  end



(* ------------------------------------------------------------- *)



(* ------------------------------------------------------------- *)

(* module type TypeSig =
 * sig
 *   type term
 *   val types_equivalent : term -> term -> bool
 *   val print : term -> string
 * end
 * 
 * (\* The two following modules, Default and NoDebug, are implementations of
 *    the TypeSig and unification.TermSig signatures. Default.term types
 *    are annotated with some debug informations inside the constructor label.
 *    NoDebug terms are bare-bones. *\)
 * 
 * module Default =
 * struct
 * 
 *   type debug_info        = string
 * 
 *   type constructor_label = debug_info * Ast.typecons
 * 
 *   type term              = constructor_label Unification.pterm
 * 
 * 
 *   let label_compatible : constructor_label -> constructor_label -> bool =
 *     fun (_, s1) (_, s2) ->
 *       s1 = s2
 * 
 *   let string_of_label : constructor_label -> string =
 *     fun (debug, label) -> label
 * 
 *   let debug_of_label : constructor_label -> string =
 *     fun (debug, label) -> debug
 * 
 * 
 * 
 *   (\* change the debug info within a type *\)
 *   let set_debug debug_info =
 *     function
 *     | TermVar v -> TermVar v
 *     | TermCons((_, label), subterms) ->
 *       TermCons((debug_info, label), subterms)
 * 
 * 
 *   (\* ugly-printing functions *\)
 * 
 *   let print x =
 *     Terms.string_of_term
 *       string_of_int
 *       string_of_label
 *       x
 * 
 *   (\* Some helpful functions : combinators to create types. *\)
 * 
 *   let mkvar v =
 *     TermVar v
 * 
 *   let make debug head subterms =
 *     TermCons((debug, head), subterms)
 * 
 *   let mk0ary debug head =
 *     TermCons((debug, head), [])
 * 
 *   let arrow_type debug dom codom =
 *     make debug "->" [ dom; codom ]
 * 
 *   let tuple_type debug  l =
 *     make debug "*" l
 * 
 *   let array_type debug t =
 *     make debug "array" [ t ]
 * 
 *   let string_type debug =
 *     make debug "string" []
 * 
 *   let float_type debug =
 *     make debug "float" []
 * 
 *   let int_type debug =
 *     make debug "int" []
 * 
 *   let int32_type debug =
 *     make debug "int32" []
 * 
 *   let int64_type debug =
 *     make debug "int64" []
 * 
 *   let nativeint_type debug =
 *     make debug "nativeint" []
 * 
 *   let char_type debug =
 *     make debug "char" []
 * 
 *   let bool_type debug =
 *     make "bool" []
 * 
 *   let unit_type debug =
 *     make debug "unit" []
 * 
 * 
 * end
 * 
 * module NoDebug =
 * struct
 * 
 *   type constructor_label = Ast.typecons
 * 
 *   type term              = constructor_label Unification.pterm
 * 
 *   let types_equivalent t1 t2 =
 *     let rec alpha_convert_type mapping seed =
 *       function
 *       | TermVar v ->
 *         if List.mem_assoc v mapping then
 *           (TermVar (List.assoc v mapping), mapping, seed)
 *         else
 *           let next = seed+1 in
 *           (TermVar seed, (v, next) :: mapping, next)
 *       | TermCons(x, subterms) ->
 *         let subterms, mapping, seed = List.fold_left (fun (subterms, mapping, seed) term ->
 *             let term, mapping, seed = alpha_convert_type mapping seed term in
 *             (term :: subterms, mapping, seed)
 *           ) ([], mapping, seed) subterms in
 *         (TermCons(x, List.rev subterms), mapping, seed)
 *     in
 *     let (t1, _, _) = alpha_convert_type [] 0 t1 in
 *     let (t2, _, _) = alpha_convert_type [] 0 t2 in
 *     t1 = t2
 * 
 *   (\* ugly-printing functions *\)
 * 
 *   let print x =
 *     Terms.string_of_term
 *       string_of_int
 *       (fun x -> x)
 *       x
 * 
 *   (\* Some helpful functions : combinators to create types. *\)
 * 
 *   let mkvar v =
 *     TermVar v
 * 
 *   let make head subterms =
 *     TermCons(head, subterms)
 * 
 *   let mk0ary head =
 *     TermCons(head, [])
 * 
 *   let arrow_type dom codom =
 *     make "->" [ dom; codom ]
 * 
 *   let tuple_type  l =
 *     make "*" l
 * 
 *   let array_type t =
 *     make "array" [ t ]
 * 
 *   let string_type =
 *     make "string" []
 * 
 *   let float_type =
 *     make "float" []
 * 
 *   let int_type =
 *     make "int" []
 * 
 *   let int32_type =
 *     make "int32" []
 * 
 *   let int64_type =
 *     make "int64" []
 * 
 *   let nativeint_type =
 *     make "nativeint" []
 * 
 *   let char_type =
 *     make "char" []
 * 
 *   let bool_type =
 *     make "bool" []
 * 
 *   let unit_type =
 *     make "unit" []
 * 
 * end
 * 
 * 
 * (\* We need a function to convert from Default to NoDebug terms. *\)
 * let forget_debug x = 
 *   Terms.term_lift
 *     (fun (debug, cons) -> cons)
 *     (fun var -> Terms.TermVar var) x *)


module AlphaTypeMap(I : S) =
struct

  type 'a t = (I.t * 'a) list

  let empty = []

  let rec mem key map =
    match map with
    | [] -> false
    | (t, _) :: tl ->
      if I.alpha_equivalent key t then
        true
      else
        mem key tl

  let rec find_opt key map =
    match map with
    | [] -> None
    | (t, elt) :: tl ->
      if I.alpha_equivalent key t then
        Some elt
      else
        find_opt key tl

  let add key elt map =
    (key, elt) :: (List.filter (fun (key', _) -> key' <> key) map)

  let rec fold f map acc =
    match map with
    | [] -> acc
    | (x, y) :: l ->
      fold f l (f x y acc)

  let fusion op map1 map2 =
    fold (fun domain codomain map ->
        match find_opt domain map with
        | None ->
          add domain codomain map
        | Some elt ->
          add domain (op elt codomain) map
      ) map1 map2

  let domain map = List.map fst map

  let codomain map = List.map snd map

end

(* Type set quotiented by alpha-equivalence. *)
module AlphaTypeSet(I : S) = 
struct
  include Set.Make(I)

  let from_set (s : I.t Pset.t) =
    Pset.fold add s empty

end

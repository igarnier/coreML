(* Ast module. *)

(* The [Ast] module defines the abstract syntax tree of our flavor
   of core ML. It is a pure call-by-value simply-typed lambda-calculus extended with~:

   - algebraic data types
   - tuples
   - pattern matching as a general elimination form for the aforementioned
     data
   - let-definitions
   - a fixpoint operator
   - some builtin types & functions

   The compiler itself is written in a pure, call-by-value subset of OCaml.

   A program is structured as a list of type definitions, in the style
   of OCaml, followed by a possibly empty list of value definitions, and ending
   with a [main] expression. During parsing (cf. [Parsing]), all these definitions are
   collapsed into one big expression. The types and terms are in first-order
   representation, care must be taken to alpha-convert them before playing with
   substitutions.

   As can be seen from the [pattern] and [expr] definition, each node
   carries an id (which should be unique), allowing us to annotate
   the AST using integer maps.
*)

open Utils
open Printf

type unique_id = int
type vvar      = string
type ident     = vvar
type datacons  = string


(* Constants *)
type constant =
  | CInt   of int
  | CChar  of char
  | CFloat of float

(* Patterns *)
type pattern = { patt_desc : patt_desc; uid : unique_id }
and patt_desc =
  | Pany
  | Pvar   of vvar
  | Pconst of constant
  | Ptuple of pattern list
  | Pconstruct of datacons * pattern option

(* Expressions *)
type expr = { expr_desc : expr_desc; uid : unique_id }
and expr_desc =
  | Eident     of { ident : ident }
  | Econstant  of { constant : constant }
  | Elet       of { binder : vvar; bound : expr; body : expr }
  | Efunction  of { arg : vvar; body : expr }
  | Efixpoint  of { fix : vvar; arg : vvar; body : expr }
  | Eapply     of { f : expr; args : expr list }
  | Ematch     of { matched : expr; matching : matching }
  | Etuple     of { exprs : expr list }
  | Econstruct of { cons : datacons; data : expr option }
and matching = rule list
and rule = { rpatt : pattern; rexpr : expr }

(* Parsed types *)
module T = 
  Types.Make(struct 
    type debug = unit 
    type var   = string
    let default = ()
    let print_debug _ = None
    let print_var v = v
  end)

type core_type = T.t

(* Our "inductive" types are just first-order variant types parameterised
   by types variables. *)
type inductive_type =
  | IndAbs    of { ind_type_var : string; ind_type : inductive_type }
  | IndIntros of { ind_intros : (datacons * core_type option) list }

type type_declaration =
  { tdecl_name : string;
    tdecl_kind : type_kind }
and type_kind =
  | Builtin
  | SumType of inductive_type

(* Items. *)
(* Note that type declarations can be mutually recursive. *)
type item = { item_desc : item_desc; uid : unique_id }
and item_desc =
  | Iexternal of { external_ident : vvar; external_type : core_type }
  | Itypedecl of type_declaration list

type decls = item list

type program = { program_decls : decls; main : expr }


(*i****************************************************************i*)

(* During the process of compilation, we will often have to manipulate
   the binders (for instance during alpha-conversion). In order to be
   able to have an intelligible result, we manage to keep the original
   identifier in prefix position. The "salt" is separated of the prefix
   by [sep_char], a constant and special-purpose character.

   This allows us to still print unmangled identifiers after all the compilation
   passes. Yes, that's also called a hack. *)

let sep_char  = char_of_int 255
let separator = String.make 1 sep_char

let (^^) a b = a^separator^b

let fresh fg s =
  let fg, fresh = Fresh.next fg in
  fg, s^^(Fresh.var fresh)

let printable_clean str =
  match String.index_opt str sep_char with
  | None   -> str
  | Some i -> String.sub str 0 i

let printable_dirty str =
  let xs = String.split_on_char sep_char str in
  match xs with
  | []      -> invalid_arg "printable_dirty: empty list"
  | [xs]    -> str
  | [hd;tl] -> 
    hd^"_"^tl
  | _ ->
    invalid_arg ("printable_dirty: list too big for str "^str)

let printable = printable_clean



(******************************************************************)

(* These are often used functions on the types, e.g. application of
   a polymorphic type to a type argument, or extraction of the introduction
   rules from a declaration. *)

(* inductive[var\arg] *)
let rec inductive_subst var arg inductive =
  match inductive with
  | IndAbs { ind_type_var; ind_type } ->
    if ind_type_var = var then
      inductive
    else
      IndAbs { ind_type_var; ind_type = inductive_subst var arg ind_type }
  | IndIntros { ind_intros } ->
    let rules = 
      List.map
        (function
          | (cons, None)        -> (cons, None)
          | (cons, Some domain) ->
            (cons, Some (Terms.term_subst var arg domain))
        ) ind_intros
    in
    IndIntros { ind_intros = rules }

let inductive_apply indtype typearg =
  match indtype with
  | IndAbs { ind_type_var; ind_type } ->
    inductive_subst ind_type_var typearg ind_type
  | IndIntros _ ->
    failwith "Ast.inductive_apply: type is not an abstraction."

let rec constructors_of_inductive_def indtype =
  match indtype with
  | IndAbs { ind_type_var; ind_type } ->
    constructors_of_inductive_def ind_type
  | IndIntros { ind_intros } -> ind_intros


(******************************************************************)

(* These are often used functions on the expressions. *)

let variables_of_pattern patt =
  let rec aux acc { patt_desc } =
    match patt_desc with
    | Pany
    | Pconst _
    | Pconstruct(_, None) -> acc
    | Pvar vvar -> vvar :: acc
    | Ptuple patts ->
      List.fold_left aux acc patts
    | Pconstruct(_, Some patt) ->
      aux acc patt
  in
  let vars = aux [] patt in
  let cond = Utils.check_uniqueness (=) (List.sort String.compare vars) in
  if cond then
    vars
  else
    failwith "Ast.variables_of_pattern : variables cannot be bound multiple times in patterns."

let variables_of_pattern_with_ids patt =
  let rec aux acc { patt_desc; uid } =
    match patt_desc with
    | Pany
    | Pconst _
    | Pconstruct(_, None) -> acc
    | Pvar vvar -> (vvar, uid) :: acc
    | Ptuple patts ->
      List.fold_left aux acc patts
    | Pconstruct(_, Some patt) ->
      aux acc patt
  in
  let vars  = aux [] patt in
  let vars' = List.map fst vars in
  let cond  = Utils.check_uniqueness (=) (List.sort String.compare vars') in
  if cond then
    vars
  else
    failwith "Ast.variables_of_pattern_with_ids: variables cannot be bound multiple times in patterns."


let remap_pattern patt f =
  let rec aux { patt_desc; uid } =
    let patt_desc = match patt_desc with
      | Pany
      | Pconst _
      | Pconstruct(_, None) -> 
        patt_desc
      | Pvar v ->
        Pvar (f v)
      | Ptuple patts ->
        Ptuple (List.map aux patts)
      | Pconstruct(cons, Some patt') ->
        Pconstruct(cons, Some (aux patt'))
    in
    { patt_desc; uid }
  in aux patt

let remap_core_type = Terms.remap_term

let rec is_value { expr_desc } =
  match expr_desc with
  | Eident _
  | Econstant _
  | Efunction _
  | Efixpoint _
  | Etuple _
  | Econstruct _ -> true
  | Elet { body } ->
    is_value body
  | _ -> false

(*i e[x\y] i*)
let rec subst x y { expr_desc; uid } =
  let desc = match expr_desc with
    | Eident { ident } ->
      if x = ident then y else expr_desc
    | Econstant _ -> 
      expr_desc
    | Elet { binder; bound; body } ->
      let bound' = subst x y bound in
      if binder = x then
        Elet { binder; bound = bound'; body }
      else
        Elet { binder; bound = bound'; body = subst x y body }
    | Efunction { arg; body } ->
      if arg = x then
        expr_desc
      else
        Efunction { arg; body = subst x y body }
    | Efixpoint { fix; arg; body } ->
      if x = fix || x = arg then
        expr_desc
      else
        Efixpoint { fix; arg; body = subst x y body }
    | Eapply { f; args } ->
      Eapply { f    = subst x y f;
               args = List.map (subst x y) args }
    | Ematch { matched; matching } ->
      let matched'  = subst x y matched in
      let matching' = 
        List.map (fun { rpatt; rexpr } ->
            if List.mem x (variables_of_pattern rpatt) then
              { rpatt; rexpr }
            else
              { rpatt; rexpr = subst x y rexpr }
          ) matching in
      Ematch { matched = matched'; matching = matching' }
    | Etuple { exprs } ->
      Etuple { exprs = List.map (subst x y) exprs }
    | Econstruct { cons; data = None } ->
      expr_desc
    | Econstruct { cons; data = Some expr } ->
      Econstruct { cons; data = Some (subst x y expr) }
  in
  { expr_desc = desc; uid }

(* Compute the free variables of a term. Every free variable
   appears exactly once. *)
let free_variables expr =
  let rec fvs env acc { expr_desc; uid } =
    match expr_desc with
    | Eident { ident } ->
      if List.mem ident env then
        acc
      else
        ((ident, uid) :: acc)
    | Econstant _ -> 
      acc
    | Elet { binder; bound; body } ->
      let acc = fvs env acc bound in
      fvs (binder :: env) acc body
    | Efunction { arg; body } ->
      fvs (arg :: env) acc body
    | Efixpoint { fix; arg; body } ->
      fvs (fix :: arg :: env) acc body
    | Eapply { f; args } ->
      let acc = fvs env acc f in
      List.fold_left (fvs env) acc args
    | Ematch { matched; matching } ->
      let acc = fvs env acc matched in
      List.fold_left (fun acc { rpatt; rexpr } ->
          let env = List.rev_append (variables_of_pattern rpatt) env in
          fvs env acc rexpr
        ) acc matching
    | Etuple { exprs } ->
      List.fold_left (fvs env) acc exprs
    | Econstruct { data = None } ->
      acc
    | Econstruct { data = Some expr } ->
      fvs env acc expr
  in
  fvs [] [] expr

(****************************************************************)

(* The following functions are used to assign unique ids to each node
   of an expression. Each function is parameterized by a fresh variable
   generator [freshgen]. The functions are hand-written in monadic style,
   threading the fresh variable generator during the recursion. The code
   may seem quite messy to the programmer for which the respective usages
   of [fold_left] and [fold_right] is not clear...

   Please note that any map relying on ids will become useless after a refresh, 
   since the key for a given node will not be the same after that refresh.
*)

let rec refresh_pattern freshgen { patt_desc } =
  let desc, freshgen = match patt_desc with
    | Ptuple patts ->
      let patts, freshgen = List.fold_right (fun p (patts, gen) ->
          let p, gen = refresh_pattern gen p in
          (p :: patts, gen)
        ) patts ([], freshgen) in
      (Ptuple patts), freshgen
    | Pconstruct(cons, Some p) ->
      let p, freshgen = refresh_pattern freshgen p in
      (Pconstruct(cons, Some p)), freshgen
    | _ -> patt_desc, freshgen
  in
  let freshgen, id = Fresh.next freshgen in
  { patt_desc = desc; uid = id }, freshgen


let rec refresh_expression freshgen { expr_desc } =
  let desc, freshgen = match expr_desc with
    | Elet { binder; bound; body } ->
      let bound, freshgen = refresh_expression freshgen bound in
      let body, freshgen  = refresh_expression freshgen body in
      Elet { binder; bound; body }, freshgen
    | Efunction { arg; body } ->
      let body, freshgen = refresh_expression freshgen body in
      Efunction { arg; body }, freshgen
    | Efixpoint { fix; arg; body } ->
      let body, freshgen = refresh_expression freshgen body in
      Efixpoint { fix; arg; body }, freshgen
    | Eapply { f; args } ->
      let func, freshgen = refresh_expression freshgen f in
      let args, freshgen = List.fold_right (fun arg (args, freshgen) ->
          let arg, freshgen = refresh_expression freshgen arg in
          (arg :: args, freshgen)
        ) args ([], freshgen) 
      in
      Eapply { f = func; args }, freshgen
    | Ematch { matched; matching } ->
      let matched, freshgen  = refresh_expression freshgen matched in
      let matching, freshgen = 
        List.fold_right (fun { rpatt; rexpr } (matching, freshgen) ->
            let rpatt, freshgen  = refresh_pattern freshgen rpatt in
            let rexpr, freshgen = refresh_expression freshgen rexpr in
            ({ rpatt; rexpr } :: matching, freshgen)
          ) matching ([], freshgen) 
      in
      Ematch { matched; matching }, freshgen
    | Etuple { exprs } ->
      let fields, freshgen = List.fold_right (fun field (fields, freshgen) ->
          let field, freshgen = refresh_expression freshgen field in
          (field :: fields, freshgen)
        ) exprs ([], freshgen)
      in
      Etuple { exprs }, freshgen
    | Econstruct { cons; data = Some e } ->
      let e, freshgen = refresh_expression freshgen e in
      Econstruct { cons; data = Some e }, freshgen
    | Econstruct _
    | Eident _
    | Econstant _ ->
      expr_desc, freshgen
  in
  let freshgen, id = Fresh.next freshgen in
  { expr_desc = desc; uid = id }, freshgen


let rec refresh_structure_item freshgen { item_desc } =
  let freshgen, id = Fresh.next freshgen in
  { item_desc; uid = id }, freshgen

let rec refresh_program freshgen { program_decls; main } =
  let freshgen, decls = List.fold_right (fun elt (freshgen, items) ->
      let item, freshgen = refresh_structure_item freshgen elt in
      (freshgen, item :: items)
    ) program_decls (freshgen, []) in
  let expr, freshgen = refresh_expression freshgen main in
  { program_decls = decls; main = expr }, freshgen


(******************************************************************)

(* Some helpful combinators to create expressions and patterns. Note that when
   using theses, the id of each node is set to -1. A call
   to [refresh_program] may be helpful after a compilation pass making
   use of theses. *)

module E =
  struct

    let expr expr_desc = { expr_desc; uid = -1 }

    let id ident = expr (Eident { ident })

    let lam arg body =
      expr (Efunction { arg; body })

    let fix fix arg body =
      expr (Efixpoint { fix; arg; body })

    let app f arg =
      expr (Eapply { f; args = [arg] })

    let appl f args =
      expr (Eapply { f; args })

    let letb binder bound body =
      expr (Elet { binder; bound; body })

    let cst constant =
      expr (Econstant { constant })

    let mtch matched matching =
      expr (Ematch { matched; matching })

    let tpl exprs =
      expr (Etuple { exprs })

    let cns1 cons e =
      expr (Econstruct { cons; data = Some e })

    let cns0 cons =
      expr (Econstruct { cons; data = None })

  end

module P =
  struct
    
    let patt patt_desc = { patt_desc; uid = -1 }

    let any = patt Pany

    let var v = patt (Pvar v)

    let cst c = patt (Pconst c)

    let cns1 cons pattern = patt (Pconstruct(cons, Some (pattern)))

    let cns0 cons = patt (Pconstruct(cons, None))

    let tpl fields = patt (Ptuple fields)

  end

let mkexpr expr_desc = { expr_desc; uid = -1 }

let mkident ident = mkexpr (Eident { ident })

let mkfun arg body =
  mkexpr (Efunction { arg; body })

let mkfix fix arg body =
  mkexpr (Efixpoint { fix; arg; body })

let mkapp f arg =
  mkexpr (Eapply { f; args = [arg] })

let mklet binder bound body =
  mkexpr (Elet { binder; bound; body })

let mkconst constant =
  mkexpr (Econstant { constant })

let mkmatch matched matching =
  mkexpr (Ematch { matched; matching })

let (|->) rpatt rexpr = { rpatt; rexpr }

let mktuple exprs =
  mkexpr (Etuple { exprs })

let mkconstruct cons data =
  mkexpr (Econstruct { cons; data })


let patt patt_desc = { patt_desc; uid = -1 }

let mkpany = patt Pany

let mkpvar v = patt (Pvar v)

let mkpconst c = patt (Pconst c)

let mkpconstruct cons pattern = patt (Pconstruct(cons, pattern))

let mkptuple fields = patt (Ptuple fields)

(******************************************************************)

(* The usual printing function. Note that identifiers are demangled
   using the [printable] function. *)

let print_constant =
  function
  | CInt i -> string_of_int i
  | CChar c -> String.make 1 c
  | CFloat f -> string_of_float f

let rec print_pattern { patt_desc } =
  let s = match patt_desc with
    | Pany -> "_"
    | Pvar v -> 
      printable v
    | Pconst c -> 
      print_constant c
    | Ptuple patts ->
      "("^(print_list "," print_pattern patts)^")"
    | Pconstruct(datacons, None) ->
      (printable datacons)
    | Pconstruct(datacons, Some patt) ->
      (printable datacons)^" "^(print_pattern patt)
  in
  s(*^"$"^(string_of_int patt_id)*)

let rec print_expr { expr_desc; uid } =
  let s = match expr_desc with
    | Eident { ident } -> 
      printable ident
    | Econstant { constant } ->
      print_constant constant
    | Elet { binder; bound; body } ->
      sprintf "let %s = %s in\n%s" 
        (printable binder) (print_expr bound) (print_expr body)
    | Efunction { arg; body } ->
      sprintf "(fun %s => %s)" (printable arg) (print_expr body)
    | Efixpoint { fix; arg; body } ->
      sprintf "(fix %s %s => %s)" (printable fix) (printable arg) (print_expr body)
    | Eapply { f; args } ->
      let f    = print_expr f in
      let args = print_list " " print_expr args in
      sprintf "(%s %s)" f args
    | Ematch { matched; matching } ->
      let e = print_expr matched in
      let m = print_matching matching in
      sprintf "match %s with [ %s ]" e m
    | Etuple { exprs } ->
      "("^(print_list "," print_expr exprs)^")"
    | Econstruct { cons; data = None } ->
      printable cons
    | Econstruct { cons; data = Some e } ->
      "("^(printable cons)^" "^(print_expr e)^")"
  in
  s(*^"$"^(string_of_int expr_id)*)

and print_matching matching =
  print_list "\n| " (fun { rpatt; rexpr } ->
      sprintf "%s => %s" (print_pattern rpatt) (print_expr rexpr)
    ) matching


(* Printing types *)

let rec print_inductive inductive =
  match inductive with
  | IndAbs { ind_type_var; ind_type } ->
    sprintf "abs %s. %s" ind_type_var (print_inductive ind_type)
  | IndIntros { ind_intros } ->
    let cons = print_list "\n| " (fun (datacons, opt_typ) ->
        match opt_typ with
        | None -> (printable datacons)
        | Some typ ->
          (printable datacons)^" :"^(T.print typ)
      ) ind_intros in
    "["^cons^"]"

let print_typedecl decl =
  let name = printable decl.tdecl_name in
  let kind = match decl.tdecl_kind with
    | Builtin -> "builtin"
    | SumType inductive ->
      print_inductive inductive
  in
  sprintf "type %s = %s;\n" name kind

let print_item { item_desc } =
  match item_desc with
  | Iexternal { external_ident; external_type } ->
    sprintf "external %s : %s;\n" external_ident (T.print external_type)
  | Itypedecl decls ->
    let s = print_list "\nand " print_typedecl decls in
    s^";\n"

let print_decls decls = List.iter (fun x -> printf "%s\n" (print_item x)) decls

let print_program { program_decls; main } =
  print_decls program_decls;
  printf "%s\n" (print_expr main)


(* -- format -- *)

let format_constant fmt =
  function
  | CInt i   -> Format.pp_print_int fmt i
  | CChar c  -> Format.pp_print_char fmt c
  | CFloat f -> Format.pp_print_float fmt f

let rec format_pattern fmt { patt_desc } =
  match patt_desc with
    | Pany -> 
      Format.pp_print_string fmt "_"
    | Pvar v ->
      Format.pp_print_string fmt v
    | Pconst c -> 
      format_constant fmt c
    | Ptuple patts ->
      Format.pp_print_string fmt "(";
      Format.pp_print_list
        ~pp_sep:(fun fmt () ->
            Format.pp_print_string fmt ",")
        format_pattern
        fmt
        patts;
      Format.pp_print_string fmt ")"
    | Pconstruct(datacons, None) ->
      Format.pp_print_string fmt (printable datacons)
    | Pconstruct(datacons, Some patt) ->
      Format.fprintf fmt "%s %a" (printable datacons) format_pattern_inner patt

and format_pattern_inner fmt ({ patt_desc } as pattern) =
  match patt_desc with
  | Pany | Pvar _ | Pconst _
  | Pconstruct(_, None) 
  | Ptuple _ ->
    format_pattern fmt pattern
  | _ ->
    Format.fprintf fmt "(@[%a@])" format_pattern pattern

let rec format_expr fmt { expr_desc; uid } =
  match expr_desc with
  | Eident { ident } -> 
    Format.pp_print_string fmt (printable ident)
  | Econstant { constant } ->
    format_constant fmt constant
  | Elet { binder; bound; body } ->
    Format.fprintf fmt "@[<v>@[<2>let %s =@ @[%a@] in@]@ %a@]"
      binder format_expr bound format_expr body
  | Efunction { arg; body } ->
    Format.fprintf fmt "@[<2>fun %s =>@ @[%a@]@]" arg format_expr_inner body
  | Efixpoint { fix; arg; body } ->
    Format.fprintf fmt "@[<2>fix %s %s =>@ @[%a@]@]" fix arg format_expr_inner body
  | Eapply { f; args } ->
    Format.fprintf fmt "@[<2>%a@ %a@]" format_expr_inner f format_args args
  | Ematch { matched; matching } ->
    (* Format.fprintf fmt "@[<v>@[<2>@[match %a with@]@. @[<h>[%a]@] @] @]" *)
    Format.fprintf fmt "@[<v>@[match %a with@]@, @[<v>[%a]@]@]@,"
      format_expr_inner matched
      format_matching matching
  | Etuple { exprs } ->
    Format.pp_print_string fmt "(";
    Format.pp_print_list
      ~pp_sep:(fun fmt () ->
          Format.pp_print_string fmt ",")
      format_expr
      fmt
      exprs;
    Format.pp_print_string fmt ")"
  | Econstruct { cons; data = None } ->
    Format.pp_print_string fmt (printable cons)
  | Econstruct { cons; data = Some e } ->
    Format.fprintf fmt "%s %a" (printable cons) format_expr_inner e

and format_expr_inner fmt ({ expr_desc; uid } as expr) =
  match expr_desc with
  | Eident _
  | Econstant _
  | Econstruct _
  | Etuple _ ->
    format_expr fmt expr
  | _ ->
    Format.fprintf fmt "(@[%a@])" format_expr expr
      
and format_args fmt exprs =
  Format.pp_print_list format_expr fmt exprs

and format_matching fmt matching =
  Format.pp_print_list
    ~pp_sep:(fun fmt () ->
        Format.fprintf fmt "|"
      )
    format_rule
    fmt
    matching

and format_rule fmt { rpatt; rexpr } =
  (* Format.fprintf fmt "@[<h>%a@ => @[%a@]@]@," format_pattern rpatt format_expr rexpr *)
  Format.fprintf fmt "@[<v>@[<h>%a @ =>@ @]@ @[%a@]@]@," format_pattern rpatt format_expr rexpr

(* (\* Printing types *\)
 * 
 * let rec print_inductive fmt inductive =
 *   match inductive with
 *   | IndAbs { ind_type_var; ind_type } ->
 *     sprintf "abs %s. %s" ind_type_var (print_inductive ind_type)
 *   | IndIntros { ind_intros } ->
 *     let cons = print_list "\n| " (fun (datacons, opt_typ) ->
 *         match opt_typ with
 *         | None -> (printable datacons)
 *         | Some typ ->
 *           (printable datacons)^" :"^(T.print typ)
 *       ) ind_intros in
 *     "["^cons^"]"
 * 
 * let print_typedecl decl =
 *   let name = printable decl.tdecl_name in
 *   let kind = match decl.tdecl_kind with
 *     | Builtin -> "builtin"
 *     | SumType inductive ->
 *       print_inductive inductive
 *   in
 *   sprintf "type %s = %s;\n" name kind
 * 
 * let print_item { item_desc } =
 *   match item_desc with
 *   | Iexternal { external_ident; external_type } ->
 *     sprintf "external %s : %s;\n" external_ident (T.print external_type)
 *   | Itypedecl decls ->
 *     let s = print_list "\nand " print_typedecl decls in
 *     s^";\n"
 * 
 * let print_decls decls = List.iter (fun x -> printf "%s\n" (print_item x)) decls
 * 
 * let print_program { program_decls; main } =
 *   print_decls program_decls;
 *   printf "%s\n" (print_expr main) *)

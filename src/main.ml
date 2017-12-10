open Batteries
open Utils
open Printf

let print_types typing { Ast.main } =
  let uid = main.Ast.uid in
  let s = Ast.print_expr main in
  let t = 
    match typing uid with 
    | None -> "None" 
    | Some x -> x 
  in
  printf "\n%s\nhas type %s .\n\n" s t

let interpret { Ast.main } =
  let db = DeBruijn.from_expr [] main in
  let s  = DeBruijn.print db in
  let _  = printf "\n\nevaluating %s\n" s in
  let nf = DeBruijn.eval db in
  let s  = DeBruijn.print nf in
    printf "result is %s\n" s

(* Initial type environment and fresh value generator *)

let initial_env =
  let unit = {
    Ast.tdecl_name = "unit";
    Ast.tdecl_kind = Ast.SumType (Ast.IndIntros { ind_intros = [("Unit", None)] })
  } in
  let bool = {
    Ast.tdecl_name = "bool";
    Ast.tdecl_kind = Ast.SumType (Ast.IndIntros { ind_intros = [("True", None); ("False", None)] })
  } in
  let int = {
    Ast.tdecl_name = "int";
    Ast.tdecl_kind = Ast.Builtin
  } in
  let float = {
    Ast.tdecl_name = "float";
    Ast.tdecl_kind = Ast.Builtin
  } in
  let env = Env.add_typedecl unit Env.empty in
  let env = Env.add_typedecl bool env in
  let env = Env.add_typedecl int env in
  let env = Env.add_typedecl float env in
    env

let fresh = Fresh.initial

(* Lexing & Parsing *)

let input = Lexing.from_channel (open_in Sys.argv.(1))

let program = Parser.program Lexer.token input

(* Ensure an unique id for each AST node *)

let program, fresh = Ast.refresh_program fresh program

(* Polymorphic type inference *)

let env, typing = Inference.typecheck (Inference.Polymorphic { for_monomorphisation = false}) initial_env program

let _ = print_types (typing ++ Option.map Inference.T.print) program

(* Monomorphisation *)

(* let fresh, program = Alphaconv.alpha_conversion fresh program *)

(* let env, fresh, typing, program = Inference.analyze initial_env fresh program *)

(* Data type specialization *)

(* module Spec = Specialization.Make(struct *)
(*   let id_typing = fun x -> Types.forget_debug (no_some (typing x)) *)
(*   let freshgen = fresh *)
(* end) *)

(* let program = Spec.perform_specialization program *)

(* let _ = Ast.print_program program *)

(* Pattern matching compilation *)

module Matching = Matching.Make(struct
  let sig_of = fun x -> Env.get_brethren_constructors x env
end)

let fresh, program = Matching.compile_program program fresh

(* let _, _, _, program = Inference.analyze initial_env fresh program *)

(* let _, typing = Inference.MonoInf.typecheck initial_env program *)

(* module Conv = Closure.Make(struct *)
(*   let id_typing = fun x -> Types.forget_debug (no_some (typing x)) *)
(* end) *)

(* let program = Conv.closure_conversion program *)

(* let fresh, program = Lambda_lifting.lambda_lift program fresh
 * 
 * let _, typing = Inference.typecheck (Inference.Polymorphic { for_monomorphisation = false}) initial_env program
 * 
 * let _ = print_types (typing ++ Option.map Inference.T.print) program *)


(* let program = Anf.perform_anf program fresh *)
(* let program = Linearize.perform_linearization program fresh *)

(* let _ = Ast.print_program program *)

let res = Ast.format_expr Format.std_formatter program.main

(* let _, typing = Inference.PolyInf.typecheck initial_env program *)

(* let _ = interpret program *)

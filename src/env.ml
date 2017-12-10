type 'a t = {
  venv      : 'a StringMap.t;
  typedecls : Ast.type_declaration StringMap.t;
  datacons  : Ast.datacons StringMap.t
}

let empty = {
  venv      = StringMap.empty;
  typedecls = StringMap.empty;
  datacons  = StringMap.empty
}

let extend env key elt =
  StringMap.add key elt env

let add_binding vvar codom env =
  { env with venv = extend env.venv vvar codom }

let add_typedecl decl env =
  match decl.Ast.tdecl_kind with
  | Ast.SumType indtype ->
    let constructors = Ast.constructors_of_inductive_def indtype in
    let datacons = List.fold_left (fun map (datacons, _) ->
        extend map datacons decl.Ast.tdecl_name
      ) env.datacons constructors in
    { env with
      typedecls = extend env.typedecls decl.Ast.tdecl_name decl;
      datacons = datacons }
  | Ast.Builtin ->
    { env with
      typedecls = extend env.typedecls decl.Ast.tdecl_name decl }


(* let add_typedecl vvar mutual_decls env = *)
(*   TODO BUG TODO BUG *)
(*   List.fold_left (fun env typedecl -> *)
(*     match typedecl.Ast.tdecl_kind with *)
(*       | Ast.SumType indtype -> *)
(*   let constructors = Ast.constructors_of_inductive_def indtype in *)
(*   let datacons = List.fold_left (fun map (datacons, _) -> *)
(*     extend map datacons typedecl.Ast.tdecl_name *)
(*   ) env.datacons constructors in *)
(*     { env with *)
(*       typedecls = extend env.typedecls typedecl.Ast.tdecl_name typedecl; *)
(*       datacons = datacons } *)
(*       | Ast.Builtin -> *)
(*   { env with *)
(*     typedecls = extend env.typedecls typedecl.Ast.tdecl_name typedecl } *)
(*   ) env mutual_decls *)


let lookup vvar env =
  try StringMap.find vvar env.venv with
  | Not_found ->
    failwith (Printf.sprintf  "\"%s\" not found in variable environment." vvar)

let mem vvar env =
  StringMap.mem vvar env.venv

let lookup_typename tname env =
  try StringMap.find tname env.typedecls with
  | Not_found ->
    failwith (Printf.sprintf "\"%s\" not found in typename environment." tname)

let lookup_datacons : Ast.datacons -> 'a t -> Ast.inductive_type * string =
  fun cons env ->
  let tname = try StringMap.find cons env.datacons with
    | Not_found ->
      failwith (Printf.sprintf "\"%s\" not found in data constructor environment." cons) 
  in
  let decl  = lookup_typename tname env in
  match decl.Ast.tdecl_kind with
  | Ast.SumType indtype ->
    (indtype, tname)
  | _ ->
    let mess = Printf.sprintf "Data constructor [%s] linked to an incoherent type declaration. Bug found." cons in
    failwith mess

let get_brethren_constructors cons env =
  let tname = try StringMap.find cons env.datacons with
    | Not_found ->
      failwith (Printf.sprintf "\"%s\" not found in data constructor environment." cons)
  in
  let decl  = lookup_typename tname env in
  match decl.Ast.tdecl_kind with
  | Ast.SumType indtype ->
    let constructors = Ast.constructors_of_inductive_def indtype in
    List.map fst constructors
  | _ ->
    let mess = Printf.sprintf "Data constructor [%s] linked to an incoherent type declaration. Bug found." cons in
    failwith mess

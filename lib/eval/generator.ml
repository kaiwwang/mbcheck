open Common.Ir
open Common_types
open Steps_printer


(* find the value in envirnment *)
let rec lookup env x =
  match env with
  | [] -> failwith "Variable not found"
  | (y, v) :: env' -> 
    if Var.id x = Var.id y then
      match v with
      | Constant (Int i) -> i
      | _ -> failwith "Expected integer value"
    else 
      lookup env' x

let rec execute (comp,env,sigma) =
  print_config (comp,env,sigma);
  match comp,env,sigma with
  | Return v,_,[] -> 
    print_value v; 
  
  | Annotate (term, _),env,sigma ->
      execute (term,env,sigma)

  | Let {binder; term; cont},env,sigma ->
      execute (term,env,(Frame (binder, cont)) :: sigma)

  | Return v,env,Frame (x, cont) :: sigma ->
      execute (cont,(Var.of_binder x, v) :: env,sigma)

  | App {func = Primitive op; args = [v1; v2]}, env, sigma -> 
    let value_of_var var = 
        match var with
        | Variable (var_name,_) -> lookup env var_name
        | Constant (Int i) -> i
        | _ -> failwith "unexpected variable"
    in
    let i1 = value_of_var v1 in
    let i2 = value_of_var v2 in
    let result = 
        match op with
        | "+" -> i1 + i2
        | "-" -> i1 - i2
        | "*" -> i1 * i2
        | "/" -> if i2 = 0 then failwith "Division by zero" else i1 / i2
        | _ -> failwith ("Unsupported operation: " ^ op)
    in
    execute (Return (Constant (Int result)), env, sigma)
    
    
  | _ ->  failwith "Invalid configuration"

let find_decl_by_name name decls =
  List.find_opt (fun decl -> Binder.name decl.decl_name = name) decls

let generate program =
  Printf.printf "Program: %s\n" (show_program program);
  match program.prog_body with
  | Some (App {func = Variable (main1, _); args = []}) ->
      let main_name = Var.name main1 in
      (match find_decl_by_name main_name program.prog_decls with
      | Some main_decl -> execute (main_decl.decl_body, [],[])
      | None -> failwith ("Function " ^ main_name ^ " not found in prog_decls"))
  | _ -> failwith "prog_body does not reference a function to execute"
      

  




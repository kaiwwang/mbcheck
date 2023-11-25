open Common.Ir
open Help_fun
open Eval_types
open Steps_printer


let rec check_and_update_mailboxes (program,comp,stack) mailbox_reference app_list =
  (* Printf.printf "%s" (print_config11 (comp,stack)); *)
  match comp,stack with
    | Return v,[] -> 
        check_var v mailbox_reference

    | Annotate (term, _),stack ->
        check_and_update_mailboxes (program,term,stack) mailbox_reference app_list

    | Let {binder; term; cont},stack ->
        check_and_update_mailboxes (program,term,(Frame (binder,[],cont)) :: stack) mailbox_reference app_list

    | LetPair {binders = _; pair = _; cont},  stack ->
        check_and_update_mailboxes (program,cont,  stack) mailbox_reference app_list

    | Seq (comp1, comp2),  stack ->
        check_and_update_mailboxes (program, comp1,  Frame (Binder.make (),[],comp2) :: stack) (mailbox_reference) app_list

    | Return v,  Frame (_, _, cont) :: stack ->
        if (check_var v mailbox_reference) then
          check_and_update_mailboxes (program, Return v,  []) mailbox_reference app_list
        else
          check_and_update_mailboxes (program, cont,  stack) mailbox_reference app_list

    | App {func; args},  stack -> 
        (match func with
        | Lam {parameters = _; body; _} -> 
              check_and_update_mailboxes (program,body,  stack) mailbox_reference app_list
        | Primitive _ -> 
              check_and_update_mailboxes (program,Return (Constant (Unit)),  stack) mailbox_reference app_list
        | Variable (func_var, _) ->
          let func_name = Var.name func_var in
          if List.mem func_var app_list then
              check_and_update_mailboxes (program,Return (Constant (Unit)),  stack) mailbox_reference app_list
          else
            let app_list' = func_var :: app_list in
            (match find_decl func_name program.prog_decls with
            | Some func_decl ->
                (match List.find_opt (fun arg -> check_var arg mailbox_reference) args with
                | Some arg ->
                    check_and_update_mailboxes (program, Return arg,  stack) mailbox_reference app_list'
                | None ->
                    check_and_update_mailboxes (program, func_decl.decl_body,  stack) mailbox_reference app_list'
                )
            | None -> failwith_and_print_buffer "Function not found")
              
            | _ -> failwith_and_print_buffer "Unhandled function expression in App"
      
          )

    | If {test = _; then_expr; else_expr},  stack -> 
        check_and_update_mailboxes (program, then_expr,  Frame (Binder.make (),[],else_expr) :: stack) mailbox_reference app_list

    | Case {term = _; branch1 = _, comp1; branch2 = _, comp2},  stack ->
        check_and_update_mailboxes (program, comp1,  Frame (Binder.make (),[],comp2) :: stack) mailbox_reference app_list

    | New _,  Frame (_, _ ,cont) :: stack ->
        check_and_update_mailboxes (program, cont,  stack) mailbox_reference app_list
    
    | Spawn comp',  stack ->
        check_and_update_mailboxes(program,comp',  stack) mailbox_reference app_list
    
    | Send {target; message = _; _},  stack ->
        if check_var target mailbox_reference then
          check_and_update_mailboxes (program, Return target,  []) mailbox_reference app_list
        else
          check_and_update_mailboxes (program, Return (Constant Unit),  stack) mailbox_reference app_list

    | Guard {target = _; pattern = _; guards; _},  stack ->
      let rec match_guards accum_conts = function
          | [] -> 
              let updated_stack = List.fold_right (fun cont stack_acc -> (Frame (Binder.make (), [], cont)) :: stack_acc) accum_conts stack in
              check_and_update_mailboxes (program, Return (Constant Unit),  updated_stack) mailbox_reference app_list
          | Receive {tag = _; payload_binders = _ ; mailbox_binder = _; cont} :: rest ->
              match_guards (cont :: accum_conts) rest
          | _ :: rest -> match_guards accum_conts rest
      in
      match_guards [] guards
        
    | _ ->  failwith "Invalid configuration"
and check_var var mailbox_reference =
  match var with
  | Variable (var,_) -> var = mailbox_reference
  | _ -> false
open Common.Ir
open Help_fun
open Eval_types
open Steps_printer

(* app_list avoid for recursion *)

let rec check_and_update_mailboxes (program,comp,stack) mailbox_reference mailbox app_list =
    (* Printf.printf "%s" (print_config11 (comp,stack));
    Hashtbl.iter (fun key value ->
        Printf.printf "  Key: %s%d, Value: %d\n" (RuntimeName.name key) (key.id) value)
        mailbox_counting;
    Printf.printf "邮箱%s%d" (Binder.name mailbox_reference)(mailbox_reference.id); *)

  
  match comp,stack with
    | Return _ ,[] -> 
        Hashtbl.find mailbox_counting mailbox

    | Annotate (term, _),stack ->
        check_and_update_mailboxes (program,term,stack) mailbox_reference mailbox app_list 

    | Let {binder = _; term; cont},stack ->
        check_and_update_mailboxes (program,term,(Frame (mailbox_reference,[],cont)) :: stack) mailbox_reference mailbox app_list 

    | LetPair {binders = _; pair = _; cont},  stack ->
        check_and_update_mailboxes (program,cont, stack) mailbox_reference mailbox app_list 

    | Seq (comp1, comp2),  stack ->
        check_and_update_mailboxes (program, comp1,Frame (mailbox_reference,[],comp2) :: stack) (mailbox_reference) mailbox app_list 

    | Return v,  Frame (new_mailbox_reference, _, cont) :: stack ->
        if (check_var v mailbox_reference) then
            add_mailbox_count mailbox 1
        else ();
        check_and_update_mailboxes (program, cont,  stack) new_mailbox_reference mailbox app_list 

    | App {func; args},  stack -> 
        (match func with
        | Lam {parameters = _; body; _} -> 
              check_and_update_mailboxes (program,body,  stack) mailbox_reference mailbox app_list 
        | Primitive _ -> 
              check_and_update_mailboxes (program,Return (Constant (Unit)),  stack) mailbox_reference mailbox app_list 
        | Variable (func_var, _) ->
          let func_name = Var.name func_var in
          let app_item = (func_var, args) in 
          if List.exists (fun (f_var, f_args) -> f_var = func_var && f_args = args) app_list then begin 
            check_and_update_mailboxes (program,Return (Constant (Unit)), stack) mailbox_reference mailbox app_list end
        else
            let app_list' = app_item :: app_list in
            (match find_decl func_name program.prog_decls with
            | Some func_decl ->
                let updated_mailbox_reference =
                  match List.mapi (fun i arg -> (i, arg)) args with
                  | [] -> mailbox_reference
                  | indexed_args ->
                      (match List.find_opt (fun (_, arg) -> check_var arg mailbox_reference) indexed_args with
                      | Some (index, _) -> 
                            let (binder, _) = List.nth func_decl.decl_parameters index in
                            add_mailbox_count mailbox 1;
                            binder
                      | None -> 
                          mailbox_reference
                      )
                in
                check_and_update_mailboxes (program, func_decl.decl_body, stack) updated_mailbox_reference mailbox app_list'
            | None -> failwith_and_print_buffer "Function not found")
              
            | _ -> failwith_and_print_buffer "Unhandled function expression in App"
      
          )

    | If {test = _; then_expr; else_expr},  stack -> 
        check_and_update_mailboxes (program, then_expr,  Frame (mailbox_reference,[],else_expr) :: stack) mailbox_reference mailbox app_list 

    | Case {term = _; branch1 = _, comp1; branch2 = _, comp2},  stack ->
        check_and_update_mailboxes (program, comp1,  Frame (mailbox_reference,[],comp2) :: stack) mailbox_reference mailbox app_list 

    | New _,  Frame (_, _ ,cont) :: stack ->
        check_and_update_mailboxes (program, cont,  stack) mailbox_reference mailbox app_list 
    
    | Spawn comp',  stack ->
        check_and_update_mailboxes(program,comp',  stack) mailbox_reference mailbox app_list 
    
    | Send {target; message = _; _},  stack ->
        if (check_var target mailbox_reference) then
            add_mailbox_count mailbox 1
        else ();
        check_and_update_mailboxes (program, Return (Constant Unit),  stack) mailbox_reference mailbox app_list 

    | Guard {target = _; pattern = _; guards; _},  stack ->
      let rec match_guards accum_conts = function
          | [] -> 
              let updated_stack = List.fold_right (fun cont stack_acc -> (Frame (mailbox_reference, [], cont)) :: stack_acc) accum_conts stack in
              check_and_update_mailboxes (program, Return (Constant Unit),  updated_stack) mailbox_reference mailbox app_list 
          | Receive {tag = _; payload_binders = _ ; mailbox_binder = _; cont} :: rest ->
              match_guards (cont :: accum_conts) rest
          | _ :: rest -> match_guards accum_conts rest
      in
      match_guards [] guards
        
    | _ ->  failwith "Invalid configuration"
and check_var var mailbox_reference =
  match var with
  | Variable (var,_) -> var.name^(string_of_int(var.id)) = mailbox_reference.name^(string_of_int(mailbox_reference.id))
  | _ -> false

let rec mailbox_counting_update mailbox all_processes = 
    let mailbox_exists = 
        Hashtbl.fold (fun mailbox' _ is_exists ->
            if mailbox' = mailbox then
                true
            else
                is_exists
        ) mailbox_counting false
    in

    if not mailbox_exists then
        Hashtbl.add mailbox_counting mailbox 0;

    let should_process1 = 
        let num = mailbox_reference_in_messages mailbox in
        if num <> 0 then begin
            add_mailbox_count mailbox num;
            true
        end
        else
            false
    in

    let should_process2 = List.exists (fun (prog, _, _, comp'', env'', stack) ->
        List.exists (fun (v, value) ->
            match value with
            | Mailbox m when m = mailbox ->
                if not mailbox_exists || (mailbox_exists && ((Hashtbl.find mailbox_counting mailbox) = 0)) then begin
                    let stack' = List.map (fun (Frame (binder, environment, comp)) ->
                        let new_binder = 
                        match List.find_opt (fun (_, value') -> value = value') environment with
                        | Some (binder_in_env, _) -> binder_in_env
                        | None -> binder 
                        in
                        Frame (new_binder, environment, comp)
                        ) stack
                    in
                    let count = check_and_update_mailboxes (prog, comp'', stack') v mailbox [] in
                    count <> 0  end
            else
                true
            | _ -> false
        ) env''
    ) all_processes
    in
    should_process1 || should_process2

and mailbox_reference_in_messages mailbox =
    Hashtbl.fold (fun _ messages acc ->
        if List.exists (fun (_, values) ->
            List.exists (function
              | Mailbox m -> m = mailbox 
              | _ -> false
            ) values
          ) messages then
            acc + 1
        else
            acc
    ) mailbox_map 0
open Common.Ir
open Eval_types
open Steps_printer
open Common
let step_limit = 30

let global_pid_counter = ref 1

let generate_new_pid () =
  let pid = !global_pid_counter in
  global_pid_counter := !global_pid_counter + 1;
  pid


let mailbox_map : (RuntimeName.t,message list) Hashtbl.t = Hashtbl.create 100
let blocked_processes : (RuntimeName.t,process) Hashtbl.t = Hashtbl.create 100


let add_process_to_blocked_list mailbox_name process =
  Hashtbl.add blocked_processes mailbox_name process
  

let substitute_in_message env target message =
  let substitute_value item =
    match item with
    | Variable (v, _) -> (
        match List.find_opt (fun (binder, _) -> Binder.name binder = v.name) env with
        | Some (_, value) -> value
        | None ->  item
      )
    | _ -> item
  in
  let substituted_target = substitute_value target in
  let substituted_message = List.map substitute_value message in
  (substituted_target, substituted_message)
  

let add_message_to_mailbox target_name message current_pid =
  match target_name with
  | Mailbox m ->
      let msg_list = 
        match Hashtbl.find_opt mailbox_map m with
          | Some msg_list -> 
            Buffer.add_string steps_buffer (Printf.sprintf "\n -> -> Process %d send a message to Mailbox: %s \u{1F4E8} -> ->\n" current_pid (m.name^(string_of_int m.id)));
            msg_list
          | None -> failwith_and_print_buffer "Mailbox not found"
      in
      Hashtbl.replace mailbox_map m (message :: msg_list);
      let updated_process = 
        match Hashtbl.find_opt blocked_processes m with
          | Some process -> 
              Hashtbl.remove blocked_processes m;
              [process]
          | _ -> []
      in
      updated_process
  | _ -> failwith_and_print_buffer "Expected a Mailbox value"
      
let extract_message tag mailboxName msg_list =
  let rec aux acc = function
    | [] -> failwith_and_print_buffer "No message with the given tag"
    | (msg_tag, _) as message :: rest ->
        if msg_tag = tag then
          begin
            Hashtbl.replace mailbox_map mailboxName (List.rev_append acc rest);
            message
          end
        else
          aux (message :: acc) rest
  in
  aux [] msg_list 
        
let bind_env msg payload_binders env target mailbox_binder =
  match msg with
  | (_, payload) ->
    if List.length payload <> List.length payload_binders then
      failwith_and_print_buffer "Payload does not match the number of binders"
    else
      let bindings = List.combine payload_binders payload in
      (match target with
      | Variable (v, _) ->
        (match List.find_opt (fun (b, _) -> Binder.name b = v.name) env with
        | Some (_, value) ->
          (mailbox_binder, value) :: bindings @ env
        | None ->
          failwith_and_print_buffer "Target variable not found in environment")
      | _ -> failwith_and_print_buffer "Expected a variable for target")

let mailbox_reference_in_messages mailbox =
  Hashtbl.fold (fun _ messages acc ->
    if acc then true
    else
      List.exists (fun (_, values) ->
        List.exists (function
          | Mailbox m -> m = mailbox 
          | _ -> false
        ) values
      ) messages
  ) mailbox_map false
      

let rec contains_one = function
    | Type.Pattern.One -> true
    | PatVar _ | Zero | Message _ -> false
    | Plus (p1, p2) | Concat (p1, p2) -> contains_one p1 || contains_one p2
    | Many p -> contains_one p


let find_free_guard guards = 
  (match List.find (function Free _ -> true | _ -> false) guards with
            |  (Free comp) -> comp
            | _ -> failwith_and_print_buffer "No Free guard matched")

let free_mailbox mailbox_binder env pid_to_check =
  match mailbox_binder with
  | Variable (binder, _) ->
      ( let matched_mailbox_name, updated_env =
        List.fold_right (fun (v, value) (acc_name, acc_env) ->
          match value with
          | Mailbox m when (binder.name ^ string_of_int binder.id) = (Binder.name v ^ string_of_int v.id) ->
              (Some m, acc_env) 
          | _ -> 
              (acc_name, (v, value) :: acc_env)
        ) env (None, [])
        in
        match matched_mailbox_name with
          | Some m -> 
              Buffer.add_string steps_buffer (Printf.sprintf "\n -> -> Process %d freed Mailbox:(%s) \u{1F535}-> ->\n" pid_to_check (m.name^(string_of_int m.id)));
              Hashtbl.remove mailbox_map m;
              updated_env,m
          | None -> failwith_and_print_buffer "Mailbox not found")
  | _ -> 
    failwith_and_print_buffer "Expected a variable for mailbox binder"   
      
let update_process_after_free (prog, pid, steps, comp, env, stack) mailbox =
  let updated_env = List.filter (fun (v, value) ->
    match value with
    | Mailbox _ -> (Binder.name v ^ string_of_int v.id) <> (RuntimeName.name mailbox^ string_of_int mailbox.id)
    | _ -> true
  ) env in
  let updated_stack = List.map (fun frame ->
    match frame with
    | Frame (binder, frame_env, frame_comp) ->
        let updated_frame_env = List.filter (fun (v, value) ->
          match value with
          | Mailbox _ -> (Binder.name v ^ string_of_int v.id) <> (RuntimeName.name mailbox^ string_of_int mailbox.id)
          | _ -> true
        ) frame_env in
        Frame (binder, updated_frame_env, frame_comp)
  ) stack in
  (prog, pid, steps, comp, updated_env, updated_stack)

let update_processes_after_free processes mailbox = 
  let new_processes =   
    (List.map (fun process ->
    update_process_after_free process mailbox
  ) processes) in
  Hashtbl.iter (fun m p ->
    let new_peocess = update_process_after_free p mailbox in
    Hashtbl.replace blocked_processes m new_peocess
  ) blocked_processes;
  new_processes
    
      
let find_decl name decls =
  List.find_opt (fun decl -> Binder.name decl.decl_name = name) decls

let bind_args_paras args params =
  List.map2 (fun arg param -> (fst param, arg)) args params
  
(* find the value in envirnment *)
let rec lookup env x =
  match env with
  | [] -> failwith_and_print_buffer "Variable not found"
  | (y, v) :: env' ->
      if Var.id x = Var.id (Var.of_binder y) then v
      else lookup env' x

let rec eval_of_var env v = 
  match v with
  | Variable (var_name, _) -> lookup env var_name
  | Pair (v1, v2) -> 
    let evaluated_v1 = eval_of_var env v1 in
    let evaluated_v2 = eval_of_var env v2 in
    Pair (evaluated_v1, evaluated_v2)
  | c -> c

let eval_args args env =
  List.map (fun arg -> eval_of_var env arg) args

let eval_of_op op v1 v2 = 
  match v1, v2 with
  | Constant(Int i1), Constant(Int i2) -> (
    match op with
    | "+" -> Int (i1 + i2)
    | "-" -> Int (i1 - i2)
    | "*" -> Int (i1 * i2)
    | "/" -> if i2 = 0 then failwith_and_print_buffer "Division by zero" else Int (i1 / i2)
    | "==" -> Bool (i1 == i2)
    | "!=" -> Bool (i1 <> i2)
    | "<" -> Bool (i1 < i2)
    | "<=" -> Bool (i1 <= i2)
    | ">" -> Bool (i1 > i2)
    | ">=" -> Bool (i1 >= i2)
    | _ -> failwith_and_print_buffer ("Unsupported operation: " ^ op)
  )
  | Constant(Bool b1), Constant(Bool b2) -> (
    match op with
    | "&&" -> Bool (b1 && b2)
    | "||" -> Bool (b1 || b2)
    | _ -> failwith_and_print_buffer ("Unsupported operation: " ^ op)
  )
  | _ -> failwith_and_print_buffer "Mismatched types or unsupported operation"
open Common.Ir
open Eval_types

let step_counts : (int, int) Hashtbl.t = Hashtbl.create 10

let counter = ref 0

let steps_buffer = Buffer.create 1024
let result_buffer = Buffer.create 1024
let process_buffer = Buffer.create 1024

let steps_buffer_print () = 
  Printf.printf "%s\n\n" (Buffer.contents steps_buffer)

let process_buffer_print () =
  (* sort pid*)
  let sorted_steps = 
    Hashtbl.fold (fun pid steps acc -> (pid, steps) :: acc) step_counts [] 
    |> List.sort (fun (pid1, _) (pid2, _) -> compare pid1 pid2)
  in
  List.iter (fun (pid, steps) ->
    let pid_str = if pid = 1 then "1(Main)" else string_of_int pid in
    Printf.printf "Total steps of PID %s: %d\n" pid_str steps
  ) sorted_steps;
  Printf.printf "\n>>>>>>>> Program done \u{2705} <<<<<<<<\n"
  

let result_buffer_print () = 
  Printf.printf "\n%s\n\n" (Buffer.contents result_buffer)

let failwith_and_print_buffer msg =
  steps_buffer_print (); 
  process_buffer_print ();
  result_buffer_print ();
  failwith msg

let show_message (tag, values) =
  let values_str = List.map show_value values |> String.concat ", " in
  Printf.sprintf "(%s, [%s])" tag values_str

let print_mailbox_map mailbox_map =
  let b = Buffer.create 100 in
  let mailboxes = Hashtbl.fold (fun m messages acc -> (m, messages) :: acc) mailbox_map [] in
  let sorted_mailboxes = List.sort (fun (m1, _) (m2, _) -> compare (RuntimeName.id m1) (RuntimeName.id m2)) mailboxes in
  List.iter (fun (m, messages) ->
    let messages_str = List.fold_left (fun acc msg -> acc ^ show_message msg ^ "; ") "" messages in
    Buffer.add_string b (Printf.sprintf "\nMailbox: %s, Messages: [%s]\n" (RuntimeName.name m ^"_"^string_of_int m.id) messages_str)
  ) sorted_mailboxes;
  Buffer.contents b

let print_blocked_processes blocked_processes =
  let b = Buffer.create 100 in
  Buffer.add_string b (Printf.sprintf "\nBlocked process:\n");
  let processes_list = Hashtbl.fold (fun m process acc -> (m, process) :: acc) blocked_processes [] in
  let sorted_processes = List.sort (fun (_, (_, pid1, _, _, _, _)) (_, (_, pid2, _, _, _, _)) -> compare pid1 pid2) processes_list in
  List.iter (fun (m, (_, pid, _, _, _, _)) ->
    Buffer.add_string b (Printf.sprintf "\n   Mailbox: %s -> ID: %d \n" (RuntimeName.name m ^"_"^string_of_int m.id) pid)
  ) sorted_processes;
  Buffer.contents b

  
(* Convert a value to its string representation. *)
let show_value v =
  match v with
  | Constant (Int i) -> Printf.sprintf "%d" i
  | Constant (Bool b) -> Printf.sprintf "%b" b
  | Constant (String s) -> Printf.sprintf "%s" s
  | Constant (Unit) -> Printf.sprintf "()"
  | Primitive (name) -> Printf.sprintf "%s" name
  | Inl v -> Printf.sprintf "Inl %s" (show_value v)
  | Inr _ -> Printf.sprintf "Inr %s" (show_value v)
  | Variable (x, _) -> Var.name x 
  | Pair (v1, v2) -> Printf.sprintf "(%s, %s)" (show_value v1) (show_value v2)
  | Lam {linear; parameters; result_type; body} ->
    let _ = linear in let _ = result_type in
    let params_str = parameters |> List.map (fun (binder, _) ->
      Printf.sprintf "%s" (Binder.name binder)) |> String.concat ", "
    in
    let body_str = show_comp body
    in
    Printf.sprintf "Lam (%s): { %s }" params_str  body_str
  | Mailbox m -> Printf.sprintf "Mailbox %s%d" m.name m.id
  | _ -> "Other value"

let name_or_id x = 
  let name = Var.name x in
  let id = string_of_int (Var.id x) in
  if name = "" then "_" ^ id else name ^ id
  
let show_env env =
  let bindings = List.map (fun (x, v) -> Printf.sprintf "%s -> %s" (name_or_id (Var.of_binder x)) (show_value v)) env in
  "[" ^ (String.concat "; " bindings) ^ "]"
  
(* Convert a frame to its string representation. *)
let show_frame (Frame (binder, env ,comp)) =
  Printf.sprintf "Frame(%s,%s,%s)" (Binder.name binder) (show_env env) (show_comp comp)

(* Convert a frame stack to its string representation. *)
let show_frame_stack stack =
  let frames = List.map show_frame stack in
  "[" ^ (String.concat "; " frames) ^ "]"

(* Print the current configuration. *)
let print_config (comp, env, stack, steps, pid, mailbox_map, blocked_processes) =
  counter := !counter + 1;
  let step_str = Printf.sprintf "\n------------------- Total step %d --------------------\n" !counter in
  let mailbox_map = print_mailbox_map mailbox_map in
  let blocked_processes = print_blocked_processes blocked_processes in
  let pid_str = if pid = 1 then "1(Main)" else string_of_int pid in
  let steps_str = Printf.sprintf "\n\nCurrent PID: %s Steps: %d\n\n" pid_str steps in
  let comp_str = Printf.sprintf "Comp: %s\n\n" (show_comp comp) in
  let env_str = Printf.sprintf "Env: %s\n\n" (show_env env) in
  let frame_stack_str = Printf.sprintf "Frame Stack: %s\n" (show_frame_stack stack) in
  step_str ^ mailbox_map^ blocked_processes ^ steps_str ^ comp_str ^ env_str ^ frame_stack_str


let print_config11 (comp, env, stack) =
  counter := !counter + 1;
  let step_str = Printf.sprintf "\n------------------- Total step %d --------------------\n" !counter in
  let comp_str = Printf.sprintf "Comp: %s\n\n" (show_comp comp) in
  let env_str = Printf.sprintf "Env: %s\n\n" (show_env env) in
  let frame_stack_str = Printf.sprintf "Frame Stack: %s\n" (show_frame_stack stack) in
  step_str ^ comp_str ^ env_str ^ frame_stack_str
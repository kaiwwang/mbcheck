open Common.Ir
open Common_types

let counter = ref 0

let steps_buffer = Buffer.create 1024
let result_buffer = Buffer.create 1024

let steps_buffer_print () = 
  Printf.printf "%s\n\n" (Buffer.contents steps_buffer)

let result_buffer_print () = 
  Printf.printf "%s\n\n" (Buffer.contents result_buffer)

let failwith_and_print_buffer msg =
  steps_buffer_print (); 
  result_buffer_print ();
  failwith msg
  
(* Convert a value to its string representation. *)
let show_value v =
  match v with
  | Constant (Int i) -> Printf.sprintf "%d" i
  | Constant (Bool b) -> Printf.sprintf "%b" b
  | Constant (String s) -> Printf.sprintf "%s" s
  | Constant (Unit) -> Printf.sprintf "()"
  | Inl v -> Printf.sprintf "Inl %s" (show_value v)
  | Inr _ -> Printf.sprintf "Inr %s" (show_value v)
  | Variable (x, _) -> Var.name x
  | Pair (v1, v2) -> Printf.sprintf "(%s, %s)" (show_value v1) (show_value v2)
  | _ -> "Other value"

let name_or_id x = 
  let name = Var.name x in
  let id = string_of_int (Var.id x) in
  if name = "" then "temp_" ^ id else name ^ id

let show_env env =
  let bindings = List.map (fun (x, v) -> Printf.sprintf "%s -> %s" (name_or_id x) (show_value v)) env in
  "[" ^ (String.concat "; " bindings) ^ "]"

(* Convert a comp to its string representation. *)
  
(* Convert a frame to its string representation. *)
let show_frame (Frame (binder, comp)) =
  Printf.sprintf "Frame(%s, %s)" (Binder.name binder) (show_comp comp)

(* Convert a frame stack to its string representation. *)
let show_frame_stack sigma =
  let frames = List.map show_frame sigma in
  "[" ^ (String.concat "; " frames) ^ "]"

(* Print the current configuration. *)
let print_config (comp, env, sigma) =
  counter := !counter + 1;
  let step_str = Printf.sprintf "\n------------------- step %d --------------------\n" !counter in
  let comp_str = Printf.sprintf "Comp: %s\n\n" (show_comp comp) in
  let env_str = Printf.sprintf "Env: %s\n\n" (show_env env) in
  let frame_stack_str = Printf.sprintf "Frame Stack: %s\n" (show_frame_stack sigma) in
  step_str ^ comp_str ^ env_str ^ frame_stack_str


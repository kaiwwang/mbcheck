(* Pre-type checking.
   This is a small, basic pass which is used to rule out basic type errors,
   but primarily exists to annotate guards and variables with interfaces for
   use in the constraint generation phase. *)
open Common
open Common_types
open Ir
open Util.Utility
open Source_code

let pretype_error msg pos_list = Errors.Pretype_error (msg,pos_list) 

module Gripers = struct
    open Format

    let arity_error pos expected_len actual_len =
        let msg =
            asprintf "Arity error. Expects %d arguments, but %d were provided."
                expected_len 
                actual_len
        in
        raise (pretype_error msg [pos])

    let message_arity_error pos tag expected_len actual_len =
        let msg =
            asprintf "Arity error. Message '%s' expects %d arguments, but %d were provided."
                tag expected_len actual_len
        in
        raise (pretype_error msg [pos])

    let unbound_variable pos var =
        let msg =
            asprintf "Unbound variable %s." var
        in
        raise (pretype_error msg [pos])

    let type_mismatch pos_list expected actual =
        let msg =
            asprintf "Type mismatch. Expected %a but got %a."                
                Pretype.pp expected
                Pretype.pp actual
        in
        raise (pretype_error msg pos_list)

    (* let type_mismatch_with_message pos custom_msg expected actual =
        let msg =
            asprintf "%s. Expected %a but got %a."
                custom_msg
                Pretype.pp expected
                Pretype.pp actual
        in
        raise (pretype_error msg) *)

    let type_mismatch_with_expected pos expected_msg actual =
        let msg =
            asprintf "Type mismatch. Expected %s but got %a."                
                expected_msg
                Pretype.pp actual
        in
        raise (pretype_error msg [pos])

    (* let empty_guards pos () =
        let msg =
            asprintf "Guards cannot be empty \n At %a" Position.pp pos
        in
        raise (pretype_error msg) *)

    let cannot_synth_empty_guards pos () =
        let msg =
            asprintf "Need at least one non-fail guard to synthesise the type for a 'guard' expression." 
        in
        raise (pretype_error msg [pos])

    let cannot_synth_fail pos () =
        let msg =
            asprintf "Cannot synthesise a type for a 'fail' guard."
        in
        raise (pretype_error msg [pos])

    let cannot_synth_sum pos term =
        let msg =
            asprintf "Cannot synthesise a type for a sum constructor %a."
                Ir.pp_value term
        in
        raise (pretype_error msg [pos])
end

(* Note: This basically works since we only have mailbox subtyping at present.
 If we were to allow subtyping on other types (e.g., records), we would need
 to expand this. *)
let check_tys pos_list expected actual =
    if expected = actual then
        ()
    else
        Gripers.type_mismatch pos_list expected actual

module PretypeEnv = struct
    type t = Pretype.t StringMap.t

    let lookup pos x (env: t) =
        let var_str = Var.unique_name x in
        match StringMap.find_opt var_str env with
            | Some x -> x
            | None -> Gripers.unbound_variable pos var_str

    let bind x =
        StringMap.add (Var.unique_name x)

    let bind_many =
        List.fold_right (fun (v, prety) acc ->
            StringMap.add (Var.unique_name v) prety acc)

    let from_list xs = bind_many xs StringMap.empty
end

module IEnv = Interface_env

(* We take a bidirectional approach. Unlike in gen_constraints,
   as with most bidirectional systems, we try and synthesise as much
   as we can, since we carry around the type environment with us and
   don't need to preserve as much contextual type information. *)
let rec synthesise_val pos ienv env value : (value * Pretype.t) =
    match value with
        | VAnnotate (v, ty) ->
            let check_ty = Pretype.of_type ty in
            let v = check_val pos ienv env v check_ty in
            VAnnotate (v, ty), check_ty
        | Atom a -> (Atom a, Pretype.PBase (Base.Atom))
        | Constant c ->
            (Constant c, Pretype.PBase (Constant.type_of c))
        | Variable (x, _) ->
            let ty = PretypeEnv.lookup pos x env in
            Variable (x, Some ty), ty
        | Primitive prim ->
            (* Look up primitive type from Lib_types *)
            (* The only way something should be parsed as a primitive
               is if its type is present in this map. *)
            let ty =
                List.assoc prim Lib_types.signatures
                |> Pretype.of_type
            in
            (Primitive prim, ty)
        | Pair (v1, v2) ->
            let (v1, ty1) = synthesise_val pos ienv env v1 in
            let (v2, ty2) = synthesise_val pos ienv env v2 in
            (Pair (v1, v2), Pretype.PPair (ty1, ty2))
        | Lam { linear; parameters; result_type; body } ->
            (* Defer linearity checking to constraint generation. *)
            let param_types  = List.map snd parameters in
            let pretype_params =
                List.map
                    (fun (b, ty) -> Var.of_binder b, Pretype.of_type ty)
                    parameters
            in
            let result_prety = Pretype.of_type result_type in
            let env = PretypeEnv.bind_many pretype_params env in
            let body = check_comp ienv env body result_prety pos in
            Lam { linear; parameters; body; result_type },
            Pretype.PFun {
                linear = linear;
                args = param_types;
                result = result_prety
            }
        | ((Inl _) as x) | ((Inr _) as x) -> Gripers.cannot_synth_sum pos x
and check_val pos ienv env value ty =
    match value, ty with
        | Inl v, (Pretype.PSum (pty1, _)) ->
            let v = check_val pos ienv env v pty1 in
            Inl v
        | Inr v, (Pretype.PSum (_, pty2)) ->
            let v = check_val pos ienv env v pty2 in
            Inr v
        | Inl _, ty | Inr _, ty ->
            raise
                (Gripers.type_mismatch_with_expected pos
                    "a sum type" ty)
        | _ ->
            let value, inferred_ty = synthesise_val pos ienv env value in
            check_tys [pos] ty inferred_ty;
            value
and synthesise_comp ienv env comp =
    let pos = WithPos.pos comp in
    let synth = synthesise_comp ienv env in
    let synthv = synthesise_val pos ienv env in
    match WithPos.node comp with
        | Annotate (c, ty) ->
            let check_ty = Pretype.of_type ty in
            let c = check_comp ienv env c check_ty pos in
            WithPos.with_pos pos(Annotate (c, ty)), check_ty
        | Return v ->
            let (v, ty) = synthv v in
            WithPos.with_pos pos(Return v), ty
        | New iname ->
            WithPos.with_pos pos(New iname), Pretype.PInterface iname
        | Spawn e ->
            let e =
                check_comp ienv env e (Pretype.PBase Unit) pos 
            in
            WithPos.with_pos pos (Spawn e), Pretype.PBase Unit
        | If { test; then_expr; else_expr } ->
            let test =
                check_val pos ienv env test (Pretype.PBase Bool)
            in
            let then_expr, ty = synth then_expr in
            let else_expr = check_comp ienv env else_expr ty pos in
            WithPos.with_pos pos(If { test; then_expr; else_expr }), ty
        | Let { binder; term; cont } ->
            let term, term_ty = synth term in
            let env' = PretypeEnv.bind (Var.of_binder binder) term_ty env in
            let cont, cont_ty = synthesise_comp ienv env' cont in
            WithPos.with_pos pos(Let { binder; term; cont }), cont_ty
        | Case { term; branch1 = ((bnd1, ty1), e1); branch2 = ((bnd2, ty2), e2) } ->
            let prety1 = Pretype.of_type ty1 in
            let prety2 = Pretype.of_type ty2 in
            let term =
                check_val pos ienv env term (Pretype.PSum (prety1, prety2))
            in
            let e1_env = PretypeEnv.bind (Var.of_binder bnd1) prety1 env in
            let e2_env = PretypeEnv.bind (Var.of_binder bnd2) prety2 env in
            let e1, e1_ty = synthesise_comp ienv e1_env e1 in
            let e2 = check_comp ienv e2_env e2 e1_ty pos in
            WithPos.with_pos pos(Case { term; branch1 = ((bnd1, ty1), e1); branch2 = ((bnd2, ty2), e2) }), e1_ty
        | LetPair { binders = ((b1, _), (b2, _)); pair; cont } ->
            let pair, pair_ty = synthv pair in
            let (t1, t2) =
                match pair_ty with
                    | Pretype.PPair (t1, t2) -> (t1, t2)
                    | _ ->
                        raise
                            (Gripers.type_mismatch_with_expected pos
                             "a pair type" pair_ty)
            in
            let env' =
                env
                |> PretypeEnv.bind (Var.of_binder b1) t1
                |> PretypeEnv.bind (Var.of_binder b2) t2
            in
            let cont, cont_ty = synthesise_comp ienv env' cont in
            WithPos.with_pos pos(LetPair { binders = ((b1, Some t1), (b2, Some t2)); pair; cont }), cont_ty
        | Seq (e1, e2) ->
            let e1 = check_comp ienv env e1 (Pretype.PBase Unit) pos in
            let e2, e2_ty = synth e2 in
            WithPos.with_pos pos(Seq (e1, e2)), e2_ty
        | App { func; args } ->
            let open Pretype in
            (* Synthesise type for function; ensure it is a function type *)
            let (func, f_ty) = synthv func in
            let arg_anns, result_ann =
                begin
                    match f_ty with
                        | PFun { args; result; _ } ->
                            List.map Pretype.of_type args, result
                        | t ->
                            Gripers.type_mismatch_with_expected pos "a function type" t
                end
            in
            (* Basic arity checking *)
            let spec_len = List.length arg_anns in
            let arg_len = List.length args in
            let () =
                if spec_len <> arg_len then
                    Gripers.arity_error pos spec_len  arg_len
            in
            (* Check argument types *)
            let args =
                List.combine args arg_anns
                |> List.map (fun (arg, arg_ty) ->
                    check_val pos ienv env arg arg_ty)
            in
            (* Synthesise result type *)
            WithPos.with_pos pos(App { func; args }), result_ann
        | Send { target; message = (tag, vals); _ } ->
            let open Pretype in
            (* Typecheck target *)
            let target, target_ty = synthv target in
            (* Ensure target has interface type *)
            begin
                match target_ty with
                    | PInterface iname ->
                        (* Check that:
                            - Message tag is contained within interface
                            - Message payload pretype matches that of the interface *)
                        let interface_withPos = IEnv.lookup iname ienv [(WithPos.pos comp)] in
                        let payload_target_tys =
                            WithPos.node interface_withPos
                            |> Interface.lookup ~pos_list:(WithPos.extract_pos_pair interface_withPos comp)  tag
                            |> List.map Pretype.of_type
                        in
                        let () =
                            let iface_len = List.length payload_target_tys in
                            let val_len = List.length vals in
                            if val_len <> iface_len then
                                Gripers.message_arity_error pos tag iface_len val_len
                        in
                        let vals =
                            List.combine vals payload_target_tys
                            |> List.map (fun (e, iface_ty) ->
                                check_val pos ienv env e iface_ty
                            )
                        in
                        WithPos.with_pos pos(
                        Send {
                            target;
                            message = (tag, vals);
                            iname = Some iname
                         }), Pretype.PBase Unit
                    | ty -> Gripers.type_mismatch_with_expected pos "an interface type" ty
            end
        | Free (v, _) ->
            let (v, v_ty) = synthv v in
            let iface =
                match v_ty with
                    | PInterface iface -> iface
                    | t -> Gripers.type_mismatch_with_expected pos "an interface type" t
            in
            WithPos.with_pos pos(Free (v, Some iface)), Pretype.PBase Unit
        | Guard { target; pattern; guards; _ } ->
            let (target, target_ty) = synthv target in
            let iname =
                match target_ty with
                    | PInterface iname -> iname
                    | t -> Gripers.type_mismatch_with_expected pos "an interface type" t
            in
            (* We can synthesise the type of a guard expression as long as it is
               not a unary 'fail' guard, in which case we need an annotation. *)
            let non_fail_guards = List.filter (not << is_fail_guard) guards
            in
            let guards, g_ty =
                match non_fail_guards with
                    | [] ->
                        Gripers.cannot_synth_empty_guards pos ()
                    | g :: gs ->
                        let g, g_ty = synth_guard ienv env iname g in
                        let gs =
                            List.map (fun g -> check_guard pos ienv env iname g g_ty) gs
                        in
                        g :: gs, g_ty
            in
            WithPos.with_pos pos(Guard { target; pattern; guards; iname = Some iname }), g_ty
and check_comp ienv env comp ty declPos =
    let pos = WithPos.pos comp in
    match WithPos.node comp with
        | Return v ->
            let v = check_val pos ienv env v ty in
            WithPos.with_pos pos (Return v)
        | Guard { target; pattern; guards; _ } when guards = [(WithPos.with_pos pos Fail)] ->
            let target, target_ty = synthesise_val pos ienv env target in
            let iname =
                match target_ty with
                    | PInterface iname -> iname
                    | t -> Gripers.type_mismatch_with_expected pos "an interface type" t
            in
            WithPos.with_pos pos (Guard { target; pattern; guards = [(WithPos.with_pos pos Fail)]; iname = Some iname })
        | _ ->
            let comp, inferred_ty = synthesise_comp ienv env comp in
            check_tys [declPos] ty inferred_ty;
            comp
and synth_guard ienv env iname g =
    let interface_withPos = IEnv.lookup iname ienv [(WithPos.pos g)] in
    let iface = WithPos.node interface_withPos in
    let pos = WithPos.pos g in
    match WithPos.node g with
        | Receive { tag; payload_binders; mailbox_binder; cont } ->
            let payload_tys = Interface.lookup ~pos_list:[(WithPos.pos interface_withPos);pos] tag iface in
            let expected_len = List.length payload_tys in
            (* Arity check *)
            let actual_len = List.length payload_binders in
            let () =
                if expected_len <> actual_len then
                    Gripers.message_arity_error pos tag expected_len actual_len
            in

            let payload_entries =
                List.combine
                    (List.map Var.of_binder payload_binders)
                    (List.map Pretype.of_type payload_tys)
            in
            let env =
                env
                |> PretypeEnv.bind_many payload_entries
                |> PretypeEnv.bind
                    (Var.of_binder mailbox_binder)
                    (Pretype.PInterface iname)
            in
            let cont, cont_ty = synthesise_comp ienv env cont in
            WithPos.with_pos pos (Receive { tag; payload_binders; mailbox_binder; cont }), cont_ty
        | Empty (x, e) ->
            let env = PretypeEnv.bind (Var.of_binder x) (Pretype.PInterface iname) env in
            let e, e_ty = synthesise_comp ienv env e in
            WithPos.with_pos pos (Empty (x, e)), e_ty
        | Fail ->
            Gripers.cannot_synth_fail pos ()
and check_guard pos ienv env iname g ty =
    let g, inferred_ty = synth_guard ienv env iname g in
    check_tys [pos] ty inferred_ty;
    g

(* Top-level typechecker *)
let check { prog_interfaces; prog_decls; prog_body } =

    (* Construct interface environment from interface list *)
    let ienv = IEnv.from_list prog_interfaces in
    let param_pretypes =
        List.map
            (fun (x, t) -> (Var.of_binder x, Pretype.of_type t))
    in

    (* At the moment, I'm doing the Haskell thing of assuming
       that all declarations can refer to each other.
       The alternative is that we have ML-style lexical scoping
       and explicit mutual blocks, which I might do later. *)
    let decl_env =
        List.map (fun d ->
            let param_tys =
                List.map (snd) d.decl_parameters in
            (Var.of_binder d.decl_name,
                Pretype.PFun {
                    linear = false;
                    args = param_tys;
                    result = Pretype.of_type d.decl_return_type
                })) (WithPos.extract_list_node prog_decls)
        |> PretypeEnv.from_list
    in

    (* Checks a declaration *)
    let check_decl d =
        let pos = WithPos.pos d in
        let node = WithPos.node d in
        (* Add parameters to environment *)
        let params = param_pretypes node.decl_parameters in
        let env = PretypeEnv.bind_many params decl_env in
        (* Typecheck according to return annotation *)
        let decl_body =
            check_comp ienv env node.decl_body (Pretype.of_type node.decl_return_type) pos
        in
        WithPos.with_pos pos { node with decl_body }
    in

    let prog_decls = List.map check_decl prog_decls in

    let prog_body, ty =
        match prog_body with
            | Some x ->
                let body, ty = synthesise_comp ienv decl_env x in
                Some body, Some ty
            | None -> None, None
    in
    { prog_interfaces; prog_decls; prog_body }, ty

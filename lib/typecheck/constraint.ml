(* A constraint is a language inclusion relation between two patterns. *)
open Common
open Type

(* The source of a constraint. *)
type constraint_source = Subtyping | Join | Combine | Intersection | Unrestricted | Guard

type t = Pattern.t * Pattern.t * constraint_source

exception Trap of string

let make p1 p2 constraint_source = p1, p2, constraint_source

let lhs (p1, _, _) = p1
let rhs (_, p2, _) = p2
let source (_, _, cs) = cs

let is_upper_bound =
    let open Pattern in
    function
        | (_, PatVar _, _) -> true
        | _ -> false

let is_lower_bound (_, p2, _) = Pattern.defined p2

(* Use default comparison function to allow set equality *)
let compare = compare

let pp ppf (p1, p2, source) =
    Format.fprintf ppf "%a ⊑ %a (source: %s)"
        Pattern.pp p1
        Pattern.pp p2
        (match source with
            | Subtyping -> "Subtyping"
            | Join -> "Join"
            | Combine -> "Combine"
            | Intersection -> "Intersection"
            | Unrestricted -> "Unrestricted"
            | Guard -> "Guard")

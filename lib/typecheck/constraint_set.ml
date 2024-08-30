(* Set of constraints, allowing n-ary unions *)
include Set.Make(Constraint)
open Common.Type
open Util.Utility
open Common.Source_code

let union_many = List.fold_left (union) empty

let single_constraint p1 p2 constraint_source =
    if p1 = p2 then empty else
        Constraint.make p1 p2 constraint_source |> singleton

let equivalence_constraint p1 p2 constraint_source =
    if p1 = p2 then empty else
        of_list [Constraint.make p1 p2 constraint_source; Constraint.make p2 p1 constraint_source]

let pp ppf x =
    Format.fprintf ppf "%a"
        (pp_print_newline_list Constraint.pp)
        (elements x)

(* Simplifies all patterns in constraints, then removes duplicates *)
let simplify =
    filter_map (fun c ->
        let (p1, p2) =
            Constraint.((lhs c |> Pattern.simplify,
                         rhs c |> Pattern.simplify))
        in
        if p1 = p2 then None else Some (Constraint.make p1 p2 (Constraint.source c)))

let pattern_variables cset =
    fold (fun x acc ->
        let pvs1,pos1 = Pattern.variables (Constraint.lhs x), Pattern.find_pos (Constraint.lhs x) in
        let pvs2,pos2 = Pattern.variables (Constraint.rhs x), Pattern.find_pos (Constraint.rhs x) in
        let set1 = StringSet.fold (fun v set -> StringPosSet.add (v, pos1) set) pvs1 StringPosSet.empty in
        let set2 = StringSet.fold (fun v set -> StringPosSet.add (v, pos2) set) pvs2 StringPosSet.empty in
        StringPosSet.union acc (StringPosSet.union set1 set2)
    ) cset StringPosSet.empty
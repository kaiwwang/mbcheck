open Common

type t

(* The source of a constraint. *)
type constraint_source = Subtyping | Join | Combine | Intersection | Unrestricted | Guard

exception Trap of string

(** Constructs a constraint from two patterns *)
val make : Type.Pattern.t -> Type.Pattern.t -> constraint_source -> t

(** Gets left-hand-side of the constraint *)
val lhs : t -> Type.Pattern.t

(** Gets right-hand-side of the constraint *)
val rhs : t -> Type.Pattern.t

(** Gets the source of the constraint *)
val source : t -> constraint_source

(** Returns 'true' if the constraint is an upper bound
    (i.e., is of the form `pat1 <= pat2` where pat2 contains no pattern variables) *)
val is_upper_bound : t -> bool

(** Returns 'true' if the constraint is a lower bound
    (i.e., is of the form `pat1 <= pvar`) *)
val is_lower_bound : t -> bool

(** Compares two constraints *)
val compare : t -> t -> int

(** Pretty-print *)
val pp : Format.formatter -> t -> unit

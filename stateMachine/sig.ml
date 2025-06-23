(** Effective Boolean Algebra *)
module type EBA = sig
  type phi
  type pred [@@deriving sexp, compare, equal, hash]

  val mk_top : pred
  val mk_bot : pred
  val mk_not : pred -> pred
  val mk_and : pred -> pred -> pred
  val mk_or : pred -> pred -> pred
  val mk_and_list : pred list -> pred
  val mk_or_list : pred list -> pred
  val join : pred list -> pred list -> pred list
  val entails : is_sat:(phi -> bool) -> pred -> pred -> bool
  val to_prop : pred -> phi
  val simp_opt : is_bot:(phi -> bool) -> pred -> pred option
end

(** Effectively Label Algebra *)
module type ELA = sig
  include EBA

  type func [@@deriving sexp, compare, equal, hash]

  val mk_ident : func

  val mk_preimage : pred -> func -> pred
  (** a \in mk_preimage p f <=> p(f(a)) *)

  val mk_image : pred -> func -> pred
  (** b \in mk_image p f <=> exists a \in p. f(a)=b *)
    
  val mk_disequal : pred -> func -> func -> pred
  val compose : func -> func -> func
end

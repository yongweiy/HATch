(** Effective Boolean Algebra *)
module type EBA = sig
  module P : sig
    type prop [@@deriving sexp, compare, equal, hash]

    val mk_true : prop
    val mk_not : prop -> prop
    val mk_and : prop -> prop -> prop
    val mk_or : prop -> prop -> prop
  end

  type pred [@@deriving sexp, compare, equal, hash]

  val to_prop : pred -> P.prop
  val from_prop : P.prop -> pred
  val mk_top : pred
  val mk_bot : pred
  val mk_not : pred -> pred
  val mk_and : pred -> pred -> pred
  val mk_or : pred -> pred -> pred
  val mk_and_list : pred list -> pred
  val mk_or_list : pred list -> pred
  val join : pred list -> pred list -> pred list
  val entails : is_sat:(P.prop -> bool) -> pred -> pred -> bool
  val to_prop : pred -> P.prop
  val simp_opt : is_bot:(P.prop -> bool) -> pred -> pred option
end

(** Effectively Label Algebra *)
module type ELA = sig
  include EBA

  type func [@@deriving sexp, compare, equal, hash]
  type ev [@@deriving sexp, compare, equal, hash]

  val ev_to_pred : ev -> pred

  val mk_ident : func
  val mk_const : ev -> func
  val force_const : func -> ev

  val mk_preimage : pred -> func -> pred
  (** a \in mk_preimage p f <=> p(f(a)) *)

  val mk_image : pred -> func -> pred
  (** b \in mk_image p f <=> exists a \in p. f(a)=b *)

  val mk_disequal : pred -> func -> func -> pred
  val compose : func -> func -> func
end

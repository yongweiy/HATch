module type PROP = sig
  type prop

  val mk_not : prop -> prop
  val mk_implies : prop -> prop -> prop
  val get_asm : prop -> prop
  val to_z3 : Z3.context -> prop -> Z3.Expr.expr
end

module type MINTERM = sig
  type mt

  val mt_to_string : mt -> string
  val string_to_mt : string -> mt
end

module type REGEX = sig
  type mt
  type reg

  val mk_not : reg -> reg
  val mk_and : reg -> reg -> reg

  module RegZ3 : sig
    type encoding

    val get_cardinal : encoding -> int
    val code_trace : encoding -> string -> mt list
  end

  val to_z3_two_reg :
    Z3.context -> reg * reg -> RegZ3.encoding * Z3.Expr.expr * Z3.Expr.expr

  val to_z3_one_reg : Z3.context -> reg -> RegZ3.encoding * Z3.Expr.expr
  val get_size : RegZ3.encoding -> reg -> int
  val reg_to_string : reg -> string
end

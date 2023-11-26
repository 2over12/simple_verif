module FuncExpr : sig
  type t = App of { name : string; args : t list } | Var of string
end

module EqCons : sig
  type t = Eq of FuncExpr.t * FuncExpr.t
end

include Theory.S with type L.A.t = EqCons.t

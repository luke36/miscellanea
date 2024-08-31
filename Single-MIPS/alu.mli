open Hardcaml

module I : sig
  type 'a t = { src1 : 'a; [@bits 32] src2 : 'a; [@bits 32] op : 'a [@bits 3] }
  [@@deriving sexp_of, hardcaml]
end

module O : sig
  type 'a t = { res : 'a; [@bits 32] is_zero : 'a }
  [@@deriving sexp_of, hardcaml]
end

val create : Scope.t -> Signal.t I.t -> Signal.t O.t
val hierarchical : Scope.t -> Signal.t I.t -> Signal.t O.t
val create_sim : Scope.t -> (Bits.t ref I.t, Bits.t ref O.t) Cyclesim.t

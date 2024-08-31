open Hardcaml

module I : sig
  type 'a t = { pc : 'a [@bits 32] } [@@deriving sexp_of, hardcaml]
end

module O : sig
  type 'a t = { instr : 'a [@bits 32] } [@@deriving sexp_of, hardcaml]
end

val create : Signal.t list -> Scope.t -> Signal.t I.t -> Signal.t O.t
val hierarchical : Signal.t list -> Scope.t -> Signal.t I.t -> Signal.t O.t

val create_sim :
  Signal.t list -> Scope.t -> (Bits.t ref I.t, Bits.t ref O.t) Cyclesim.t

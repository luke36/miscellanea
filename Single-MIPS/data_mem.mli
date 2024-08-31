open Hardcaml

module I : sig
  type 'a t = {
    clock : 'a;
    addr : 'a; [@bits 32]
    write_data : 'a; [@bits 32]
    write_enable : 'a;
  }
  [@@deriving sexp_of, hardcaml]
end

module O : sig
  type 'a t = { read_data : 'a [@bits 32] } [@@deriving sexp_of, hardcaml]
end

val create : int -> Scope.t -> Signal.t I.t -> Signal.t O.t
val hierarchical : int -> Scope.t -> Signal.t I.t -> Signal.t O.t
val create_sim : int -> Scope.t -> (Bits.t ref I.t, Bits.t ref O.t) Cyclesim.t

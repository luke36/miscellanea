open Hardcaml

module I : sig
  type 'a t = {
    clock : 'a;
    write_enable : 'a;
    read_addr1 : 'a; [@bits 5]
    read_addr2 : 'a; [@bits 5]
    write_addr : 'a; [@bits 5]
    write_data : 'a; [@bits 32]
  }
  [@@deriving sexp_of, hardcaml]
end

module O : sig
  type 'a t = {
    read_data1 : 'a; [@bits 32]
    read_data2 : 'a; [@bits 32]
    r31_output : 'a; [@bits 32]
  }
  [@@deriving sexp_of, hardcaml]
end

val create : Scope.t -> Signal.t I.t -> Signal.t O.t
val hierarchical : Scope.t -> Signal.t I.t -> Signal.t O.t
val create_sim : Scope.t -> (Bits.t ref I.t, Bits.t ref O.t) Cyclesim.t

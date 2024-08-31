open Hardcaml

module I : sig
  type 'a t = { op : 'a; [@bits 6] func : 'a [@bits 6] }
  [@@deriving sexp_of, hardcaml]
end

module O : sig
  type 'a t = {
    mem_to_reg : 'a;
    mem_write : 'a;
    branch : 'a;
    alu_control : 'a; [@bits 3]
    alu_src : 'a;
    reg_dst : 'a;
    reg_write : 'a;
    jump : 'a;
  }
  [@@deriving sexp_of, hardcaml]
end

val create : Scope.t -> Signal.t I.t -> Signal.t O.t
val hierarchical : Scope.t -> Signal.t I.t -> Signal.t O.t
val create_sim : Scope.t -> (Bits.t ref I.t, Bits.t ref O.t) Cyclesim.t

open Hardcaml
open Hardcaml.Signal

module I = struct
  type 'a t = { pc : 'a [@bits 32] } [@@deriving sexp_of, hardcaml]
end

module O = struct
  type 'a t = { instr : 'a [@bits 32] } [@@deriving sexp_of, hardcaml]
end

let create instrs scope (input : t I.t) : Signal.t O.t =
  let ( -- ) = Scope.naming scope in
  let instr = mux (srl input.pc 2) instrs -- "instr" in
  { instr }

let hierarchical instrs (scope : Scope.t) (input : Signal.t I.t) =
  let module H = Hierarchy.In_scope (I) (O) in
  H.hierarchical ~scope ~name:"instruction_memory" (create instrs) input

let create_sim instrs scope =
  let module Sim = Cyclesim.With_interface (I) (O) in
  Sim.create (create instrs scope)

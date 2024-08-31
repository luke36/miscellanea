open Hardcaml
open Hardcaml.Signal

module I = struct
  type 'a t = {
    clock : 'a;
    addr : 'a; [@bits 32]
    write_data : 'a; [@bits 32]
    write_enable : 'a;
  }
  [@@deriving sexp_of, hardcaml]
end

module O = struct
  type 'a t = { read_data : 'a [@bits 32] } [@@deriving sexp_of, hardcaml]
end

let create size scope (input : Signal.t I.t) : Signal.t O.t =
  let ( -- ) = Scope.naming scope in
  let write_port =
    {
      write_clock = input.clock;
      write_address = input.addr;
      write_data = input.write_data;
      write_enable = input.write_enable;
    }
  in
  let q =
    multiport_memory ~name:"data_memory" size ~read_addresses:[| input.addr |]
      ~write_ports:[| write_port |]
  in
  let read_data = q.(0) -- "read_data" in
  { read_data }

let hierarchical size (scope : Scope.t) (input : Signal.t I.t) =
  let module H = Hierarchy.In_scope (I) (O) in
  H.hierarchical ~scope ~name:"data_memory" (create size) input

let create_sim size scope =
  let module Sim = Cyclesim.With_interface (I) (O) in
  Sim.create (create size scope)

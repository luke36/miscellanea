open Hardcaml
open Hardcaml.Signal

module I = struct
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

module O = struct
  type 'a t = {
    read_data1 : 'a; [@bits 32]
    read_data2 : 'a; [@bits 32]
    r31_output : 'a; [@bits 32]
  }
  [@@deriving sexp_of, hardcaml]
end

let create scope (input : Signal.t I.t) : Signal.t O.t =
  let ( -- ) = Scope.naming scope in
  (* should this be a memory or should I manually create 32 regs? *)
  let write_port =
    {
      write_clock = input.clock;
      write_address = input.write_addr;
      write_enable = input.write_enable;
      write_data = input.write_data;
    }
  in
  let rf =
    multiport_memory ~name:"register_file" 32
      ~read_addresses:
        [| input.read_addr1; input.read_addr2; of_int ~width:5 31 |]
      ~write_ports:[| write_port |]
  in
  let read_data1 = rf.(0) -- "RD1" in
  let read_data2 = rf.(1) -- "RD2" in
  let r31 = rf.(2) -- "OUT" in
  { read_data1; read_data2; r31_output = r31 }

let hierarchical (scope : Scope.t) (input : Signal.t I.t) =
  let module H = Hierarchy.In_scope (I) (O) in
  H.hierarchical ~scope ~name:"register_file" create input

let create_sim scope =
  let module Sim = Cyclesim.With_interface (I) (O) in
  Sim.create (create scope)

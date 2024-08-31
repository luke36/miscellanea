open Hardcaml
open Hardcaml.Signal

module I = struct
  type 'a t = { src1 : 'a; [@bits 32] src2 : 'a; [@bits 32] op : 'a [@bits 3] }
  [@@deriving sexp_of, hardcaml]
end

module O = struct
  type 'a t = { res : 'a; [@bits 32] is_zero : 'a }
  [@@deriving sexp_of, hardcaml]
end

let create scope (input : Signal.t I.t) : Signal.t O.t =
  let ( -- ) = Scope.naming scope in
  let zero32 = zero 32 in
  let op2 = input.op.:[(2, 2)] in
  let src1 = input.src1 in
  let src2 = mux2 op2 ~:(input.src2) input.src2 in
  let adder = src1 +: src2 +: uresize op2 32 in
  let res =
    mux
      input.op.:[(1, 0)]
      [ src1 &: src2; src1 |: src2; adder; uresize adder.:[(31, 31)] 32 ]
    -- "alu_result"
  in
  let is_zero = (res ==: zero32) -- "is_zero" in
  { res; is_zero }

let hierarchical (scope : Scope.t) (input : Signal.t I.t) =
  let module H = Hierarchy.In_scope (I) (O) in
  H.hierarchical ~scope ~name:"ALU" create input

let create_sim scope =
  let module Sim = Cyclesim.With_interface (I) (O) in
  Sim.create (create scope)
